{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, FlexibleInstances  #-}
{-# LANGUAGE GADTs, GeneralizedNewtypeDeriving, PatternGuards                 #-}
{-# LANGUAGE LiberalTypeSynonyms, MultiParamTypeClasses, OverlappingInstances #-}
{-# LANGUAGE PolyKinds, RankNTypes, ScopedTypeVariables, StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies, TypeOperators, UndecidableInstances, ViewPatterns  #-}
{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-type-defaults                    #-}
module Algebra.Ring.PolynomialOld
    ( Polynomial, Monomial, MonomialOrder, EliminationType, EliminationOrder
    , WeightedEliminationOrder, eliminationOrder, weightedEliminationOrder
    , lex, revlex, graded, grlex, grevlex, productOrder, productOrder'
    , transformMonomial, WeightProxy(..), weightOrder, totalDegree, totalDegree'
    , IsPolynomial, coeff, lcmMonomial, sPolynomial, polynomial
    , castMonomial, castPolynomial, toPolynomial, changeOrder, changeOrderProxy
    , scastMonomial, scastPolynomial, OrderedPolynomial, showPolynomialWithVars, showPolynomialWith, showRational
    , normalize, injectCoeff, varX, var, getTerms, shiftR, orderedBy
    , divs, tryDiv, fromList, Coefficient(..),ToWeightVector(..)
    , leadingTerm, leadingMonomial, leadingOrderedMonomial, leadingCoeff, genVars, sArity
    , OrderedMonomial(..), Grevlex(..)
    , Revlex(..), Lex(..), Grlex(..), Graded(..)
    , ProductOrder (..), WeightOrder(..), subst, diff
    , IsOrder(..), IsMonomialOrder)  where
import           Algebra.Internal
import           Algebra.Ring.Noetherian
import           Algebra.Scalar
import           Control.Arrow
import           Control.DeepSeq
import           Control.Lens            hiding (assign)
import           Data.Function
import           Data.List               (intercalate)
import           Data.Map                (Map)
import qualified Data.Map.Strict         as M
import           Data.Maybe
import           Data.Monoid
import           Data.Ord
import           Data.Ratio
import Data.Hashable
import           Data.Type.Monomorphic
import           Numeric.Decidable.Units
import           Numeric.Decidable.Zero
import           Data.Type.Natural       hiding (max, one, promote, zero)
import           Data.Vector.Sized       (Vector (..))
import qualified Data.Vector.Sized       as V
import qualified Numeric.Ring.Class as   NA
import           Numeric.Algebra         hiding (Order (..))
import           Prelude                 hiding (lex, negate, recip, sum, (*),
                                          (+), (-), (^), (^^), subtract)
import qualified Prelude                 as P
import Control.Applicative

instance (IsPolynomial r n, IsOrder ord, DecidableZero r) => DecidableZero (OrderedPolynomial r ord n) where
    isZero poly = totalDegree' poly == 0 && isZero (coeff (fromList sing []) poly)

instance (IsPolynomial r n, IsOrder ord, DecidableUnits r) => DecidableUnits (OrderedPolynomial r ord n)  where
    recipUnit f | totalDegree' f > 0 = Nothing
                | otherwise          = injectCoeff <$> recipUnit (coeff (fromList sing []) f)

instance Hashable Natural where
  hash = hash . toInteger
  hashWithSalt s = hashWithSalt s . toInteger

-- | N-ary Monomial. IntMap contains degrees for each x_i.
type Monomial (n :: Nat) = Vector Natural n

instance (NFData (Monomial n)) => NFData (OrderedMonomial ord n) where
  rnf (OrderedMonomial m) = rnf m `seq` ()

instance (NFData (Monomial n), NFData r) => NFData (OrderedPolynomial r ord n) where
  rnf (Polynomial dic) = rnf dic

-- | convert NAry list into Monomial.
fromList :: SNat n -> [Natural] -> Monomial n
fromList SZ _ = Nil
fromList (SS n) [] = 0 :- fromList n []
fromList (SS n) (x : xs) = x :- fromList n xs

-- | Monomial order (of degree n). This should satisfy following laws:
-- (1) Totality: forall a, b (a < b || a == b || b < a)
-- (2) Additivity: a <= b ==> a + c <= b + c
-- (3) Non-negative: forall a, 0 <= a
type MonomialOrder = forall n. Monomial n -> Monomial n -> Ordering

totalDegree :: Monomial n -> Natural
totalDegree = V.foldl (+) 0
{-# INLINE totalDegree #-}

totalDegree' :: OrderedPolynomial k ord n -> Natural
totalDegree' = maximum . (0:) . map (totalDegree . snd) . getTerms

-- | Lexicographical order. This *is* a monomial order.
lex :: MonomialOrder
lex Nil Nil = EQ
lex (x :- xs) (y :- ys) = x `compare` y <> xs `lex` ys
lex _ _ = bugInGHC

-- | Reversed lexicographical order. This is *not* a monomial order.
revlex :: Monomial n -> Monomial n -> Ordering
revlex (x :- xs) (y :- ys) = xs `revlex` ys <> y `compare` x
revlex Nil       Nil       = EQ
revlex _ _ = bugInGHC

-- | Convert ordering into graded one.
graded :: (Monomial n -> Monomial n -> Ordering) -> (Monomial n -> Monomial n -> Ordering)
graded cmp xs ys = comparing totalDegree xs ys <> cmp xs ys
{-# INLINE graded #-}
{-# RULES
"graded/grevlex" graded grevlex = grevlex
"graded/grlex"   graded grlex   = grlex
  #-}

-- | Graded lexicographical order. This *is* a monomial order.
grlex :: MonomialOrder
grlex = graded lex
{-# INLINE grlex #-}

-- | Graded reversed lexicographical order. This *is* a monomial order.
grevlex :: MonomialOrder
grevlex = graded revlex
{-# INLINE grevlex #-}

-- | A wrapper for monomials with a certain (monomial) order.
newtype OrderedMonomial (ordering :: *) n = OrderedMonomial { getMonomial :: Monomial n }
deriving instance (Eq (Monomial n)) => Eq (OrderedMonomial ordering n)

instance Wrapped (Monomial n) (Monomial m) (OrderedMonomial o n) (OrderedMonomial o' m) where
  wrapped = iso OrderedMonomial getMonomial

-- | Class to lookup ordering from its (type-level) name.
class IsOrder (ordering :: *) where
  cmpMonomial :: Proxy ordering -> MonomialOrder

-- * Names for orderings.
--   We didn't choose to define one single type for ordering names for the extensibility.
-- | Lexicographical order
data Lex = Lex
           deriving (Show, Eq, Ord)

-- | Reversed lexicographical order
data Revlex = Revlex
              deriving (Show, Eq, Ord)

-- | Graded reversed lexicographical order. Same as @Graded Revlex@.
data Grevlex = Grevlex
               deriving (Show, Eq, Ord)

-- | Graded lexicographical order. Same as @Graded Lex@.
data Grlex = Grlex
             deriving (Show, Eq, Ord)

-- | Graded order from another monomial order.
data Graded ord = Graded ord
                  deriving (Read, Show, Eq, Ord)

instance IsOrder ord => IsOrder (Graded ord) where
  cmpMonomial Proxy = graded (cmpMonomial (Proxy :: Proxy ord))

instance IsMonomialOrder ord => IsMonomialOrder (Graded ord)

data ProductOrder (n :: Nat) (a :: *) (b :: *) where
  ProductOrder :: SNat n -> ord -> ord' -> ProductOrder n ord ord'

productOrder :: forall ord ord' n m. (IsOrder ord, IsOrder ord', SingRep n)
             => Proxy (ProductOrder n ord ord') -> Monomial m -> Monomial m -> Ordering
productOrder _ m m' =
  case sing :: SNat n of
    n -> case (V.splitAtMost n m, V.splitAtMost n m') of
           ((xs, xs'), (ys, ys')) -> cmpMonomial (Proxy :: Proxy ord) xs ys <> cmpMonomial (Proxy :: Proxy ord') xs' ys'

productOrder' :: forall n ord ord' m.(IsOrder ord, IsOrder ord')
              => SNat n -> ord -> ord' -> Monomial m -> Monomial m -> Ordering
productOrder' n ord ord' =
  case singInstance n of SingInstance -> productOrder (toProxy $ ProductOrder n ord ord')

data WeightProxy (v :: [Nat]) where
  NilWeight  :: WeightProxy '[]
  ConsWeight :: SNat n -> WeightProxy v -> WeightProxy (n ': v)

data WeightOrder (v :: [Nat]) (ord :: *) where
  WeightOrder :: WeightProxy (v :: [Nat]) -> ord -> WeightOrder v ord

class ToWeightVector (vs :: [Nat]) where
  calcOrderWeight :: Proxy vs -> Vector Natural n -> Natural

instance ToWeightVector '[] where
  calcOrderWeight Proxy _ = 0

instance (SingRep n, ToWeightVector ns) => ToWeightVector (n ': ns) where
  calcOrderWeight Proxy Nil = 0
  calcOrderWeight Proxy (x :- xs) = x * fromIntegral (sNatToInt (sing :: SNat n) )+ calcOrderWeight (Proxy :: Proxy ns) xs

weightOrder :: forall ns ord m. (ToWeightVector ns, IsOrder ord)
            => Proxy (WeightOrder ns ord) -> Monomial m -> Monomial m -> Ordering
weightOrder Proxy m m' = comparing (calcOrderWeight (Proxy :: Proxy ns)) m m'
                         <> cmpMonomial (Proxy :: Proxy ord) m m'

instance (ToWeightVector ws, IsOrder ord) => IsOrder (WeightOrder ws ord) where
  cmpMonomial p = weightOrder p

instance (IsOrder ord, IsOrder ord', SingRep n) => IsOrder (ProductOrder n ord ord') where
  cmpMonomial p = productOrder p

-- They're all total orderings.
instance IsOrder Grevlex where
  cmpMonomial _ = grevlex

instance IsOrder Revlex where
  cmpMonomial _ = revlex

instance IsOrder Lex where
  cmpMonomial _ = lex

instance IsOrder Grlex where
  cmpMonomial _ = grlex

-- | Class for Monomial orders.
class IsOrder name => IsMonomialOrder name where

-- Note that Revlex is not a monomial order.
-- This distinction is important when we calculate a quotient or Groebner basis.
instance IsMonomialOrder Grlex
instance IsMonomialOrder Grevlex
instance IsMonomialOrder Lex
instance (SingRep n, IsMonomialOrder o, IsMonomialOrder o') => IsMonomialOrder (ProductOrder n o o')
instance (ToWeightVector ws, IsMonomialOrder ord) => IsMonomialOrder (WeightOrder ws ord)

-- | Monomial order which can be use to calculate n-th elimination ideal.
-- This should judge it as bigger that contains variables to eliminate.
class (IsMonomialOrder ord, SingRep n) => EliminationType n ord
instance SingRep n => EliminationType n Lex
instance (SingRep n, IsMonomialOrder ord, IsMonomialOrder ord') => EliminationType n (ProductOrder n ord ord')
instance (IsMonomialOrder ord) => EliminationType Z (WeightOrder '[] ord)
instance (IsMonomialOrder ord, ToWeightVector ns, EliminationType n (WeightOrder ns ord))
    => EliminationType (S n) (WeightOrder (One ': ns) ord)

type EliminationOrder n = ProductOrder n Grevlex Grevlex

eliminationOrder :: SNat n -> EliminationOrder n
eliminationOrder n =
  case singInstance n of
    SingInstance -> ProductOrder n Grevlex Grevlex

weightedEliminationOrder :: SNat n -> WeightedEliminationOrder n Grevlex
weightedEliminationOrder n = WEOrder n (Proxy :: Proxy Grevlex)

type family EWeight (n :: Nat) :: [Nat]
type instance EWeight Z = '[]
type instance EWeight (S n) = One ': EWeight n

data WeightedEliminationOrder (n :: Nat) (ord :: *) where
    WEOrder :: SNat n -> Proxy ord -> WeightedEliminationOrder n ord

instance (SingRep n, IsMonomialOrder ord) => IsOrder (WeightedEliminationOrder n ord) where
  cmpMonomial Proxy m m' = comparing (calc (sing :: SNat n)) m m' <> cmpMonomial (Proxy :: Proxy ord) m m'
    where
      calc :: SNat l -> Vector Natural m -> Natural
      calc (SS _) Nil = 0
      calc SZ _ = 0
      calc (SS l) (x :- xs)= x + calc l xs

instance (SingRep n, IsMonomialOrder ord) => IsMonomialOrder (WeightedEliminationOrder n ord)

instance (SingRep n, IsMonomialOrder ord) => EliminationType n (WeightedEliminationOrder n ord) where

-- | Special ordering for ordered-monomials.
instance (Eq (Monomial n), IsOrder name) => Ord (OrderedMonomial name n) where
  OrderedMonomial m `compare` OrderedMonomial n = cmpMonomial (Proxy :: Proxy name) m n

-- | For simplicity, we choose grevlex for the default monomial ordering (for the sake of efficiency).
instance (Eq (Monomial n)) => Ord (Monomial n) where
  compare = grevlex

deriving instance (DecidableZero r, DecidableUnits r, SingRep n, IsOrder ord, NoetherianRing r, Ord r, Ord (OrderedMonomial ord n))
               => Ord (OrderedPolynomial r ord n)

-- | n-ary polynomial ring over some noetherian ring R.
newtype OrderedPolynomial r order n = Polynomial { terms :: Map (OrderedMonomial order n) r }
type Polynomial r = OrderedPolynomial r Grevlex

-- | Type-level constraint to check whether it forms polynomial ring or not.
type IsPolynomial r n = (DecidableUnits r, DecidableZero r, NoetherianRing r, SingRep n)

-- | coefficient for a degree.
coeff :: (IsOrder order, IsPolynomial r n) => Monomial n -> OrderedPolynomial r order n -> r
coeff d = M.findWithDefault zero (OrderedMonomial d) . terms

instance Wrapped (Map (OrderedMonomial order n) r) (Map (OrderedMonomial order' m) q)
                 (OrderedPolynomial r order n)     (OrderedPolynomial q order' m) where
    wrapped = iso Polynomial  terms

castMonomial :: (IsOrder o, IsOrder o', SingRep m, n :<= m) => OrderedMonomial o n -> OrderedMonomial o' m
castMonomial = unwrapped %~ fromList sing . V.toList

scastMonomial :: (n :<= m) => SNat m -> OrderedMonomial o n -> OrderedMonomial o m
scastMonomial sdim = unwrapped %~ fromList sdim . V.toList

castPolynomial :: (IsPolynomial r n, IsPolynomial r m, SingRep m, IsOrder o, IsOrder o', n :<= m)
               => OrderedPolynomial r o n
               -> OrderedPolynomial r o' m
castPolynomial = unwrapped %~ M.mapKeys castMonomial

scastPolynomial :: (IsOrder o, IsOrder o', IsPolynomial r n, IsPolynomial r m, n :<= m, SingRep m)
                => SNat m -> OrderedPolynomial r o n -> OrderedPolynomial r o' m
scastPolynomial _ = castPolynomial

normalize :: (DecidableZero r, IsOrder order, IsPolynomial r n)
          => OrderedPolynomial r order n -> OrderedPolynomial r order n
normalize = unwrapped %~ M.insertWith (+) (OrderedMonomial $ {-# SCC "replicate" #-} V.replicate' 0) zero
                       . M.filter (not . isZero)

instance (Eq r, IsOrder order, IsPolynomial r n) => Eq (OrderedPolynomial r order n) where
  Polynomial f == Polynomial g = f == g

injectCoeff :: (IsPolynomial r n) => r -> OrderedPolynomial r order n
injectCoeff r = Polynomial $ M.singleton (OrderedMonomial $ fromList sing []) r

-- | By Hilbert's finite basis theorem, a polynomial ring over a noetherian ring is also a noetherian ring.
instance (IsOrder order, IsPolynomial r n) => NoetherianRing (OrderedPolynomial r order n) where
instance (IsOrder order, IsPolynomial r n) => Ring (OrderedPolynomial r order n) where
instance (IsOrder order, IsPolynomial r n) => Rig (OrderedPolynomial r order n) where
instance (IsOrder order, IsPolynomial r n) => Group (OrderedPolynomial r order n) where
  negate (Polynomial dic) = Polynomial $ fmap negate dic
instance (IsOrder order, IsPolynomial r n) => LeftModule Integer (OrderedPolynomial r order n) where
  n .* Polynomial dic = Polynomial $ fmap (n .*) dic
instance (IsOrder order, IsPolynomial r n) => RightModule Integer (OrderedPolynomial r order n) where
  (*.) = flip (.*)
instance (IsOrder order, IsPolynomial r n) => Additive (OrderedPolynomial r order n) where
  (Polynomial f) + (Polynomial g) = normalize $ Polynomial $ M.unionWith (+) f g
instance (IsOrder order, IsPolynomial r n) => Monoidal (OrderedPolynomial r order n) where
  zero = injectCoeff zero
instance (IsOrder order, IsPolynomial r n) => LeftModule Natural (OrderedPolynomial r order n) where
  n .* Polynomial dic = Polynomial $ fmap (n .*) dic
instance (IsOrder order, IsPolynomial r n) => RightModule Natural (OrderedPolynomial r order n) where
  (*.) = flip (.*)
instance (IsOrder order, IsPolynomial r n) => Unital (OrderedPolynomial r order n) where
  one = injectCoeff one
instance (IsOrder order, IsPolynomial r n) => Multiplicative (OrderedPolynomial r order n) where
  Polynomial (M.toList -> d1) *  Polynomial (M.toList -> d2) =
    let dic = [ (OrderedMonomial $ V.zipWithSame (+) a b, r * r') | (getMonomial -> a, r) <- d1, (getMonomial -> b, r') <- d2 ]
    in normalize $ Polynomial $ M.fromListWith (+) dic
instance (IsOrder order, IsPolynomial r n) => Semiring (OrderedPolynomial r order n) where
instance (IsOrder order, IsPolynomial r n) => Commutative (OrderedPolynomial r order n) where
instance (IsOrder order, IsPolynomial r n) => Abelian (OrderedPolynomial r order n) where
instance (IsOrder order, IsPolynomial r n) => LeftModule (Scalar r) (OrderedPolynomial r order n) where
  Scalar r .* Polynomial dic = normalize $ Polynomial $ fmap (r*) dic
instance (IsOrder order, IsPolynomial r n) => RightModule (Scalar r) (OrderedPolynomial r order n) where
  Polynomial dic *. Scalar r = normalize $ Polynomial $ fmap (r*) dic

instance (Eq r, IsPolynomial r n, IsOrder order, Show r) => Show (OrderedPolynomial r order n) where
  show = showPolynomialWithVars [(n, "X_"++ show n) | n <- [0..]]

instance (SingRep n, IsOrder order) => Show (OrderedPolynomial Rational order n) where
  show = showPolynomialWith [(n, "X_"++ show n) | n <- [0..]] showRational

showPolynomialWithVars :: ( Show a, IsPolynomial a n, IsOrder ordering)
                       => [(Int, String)] -> OrderedPolynomial a ordering n -> String
showPolynomialWithVars dic p0@(Polynomial d)
    | isZero p0 = "0"
    | otherwise = intercalate " + " $ mapMaybe showTerm $ M.toDescList d
    where
      showTerm (getMonomial -> deg, c)
          | isZero c = Nothing
          | otherwise =
              let cstr = if (isOne c)
                         then if any (not . isZero) (V.toList deg) then "-" else "-1"
                         else if (not (isOne c)  || isConstantMonomial deg)
                              then show c ++ " "
                              else ""
              in Just $ cstr ++ unwords (mapMaybe showDeg (zip [1..] $ V.toList deg))
      showDeg (n, p) | p == 0    = Nothing
                     | p == 1    = Just $ showVar n
                     | otherwise = Just $ showVar n ++ "^" ++ show p
      showVar n = fromMaybe ("X_" ++ show n) $ lookup n dic

isMinusOne, isOne :: (Unital a, DecidableZero a, Group a) => a -> Bool
isOne = isZero . subtract one
isMinusOne = isZero . (+ one)

data Coefficient = Zero | Negative String | Positive String | Eps
                 deriving (Show, Eq, Ord)

showRational :: (Integral a, Show a) => Ratio a -> Coefficient
showRational r | r == 0    = Zero
               | r >  0    = Positive $ formatRat r
               | otherwise = Negative $ formatRat $ abs r
  where
    formatRat q | denominator q == 1 = show $ numerator q
                | otherwise          = show (numerator q) ++ "/" ++ show (denominator q) ++ " "

showPolynomialWith  :: (Show a, IsPolynomial a n, IsOrder ordering)
                    => [(Int, String)] -> (a -> Coefficient) -> OrderedPolynomial a ordering n -> String
showPolynomialWith vDic showCoeff p0@(Polynomial d)
    | isZero p0 = "0"
    | otherwise  = catTerms $ mapMaybe procTerm $ M.toDescList d
    where
      catTerms [] = "0"
      catTerms (x:xs) = concat $ showTerm True x : map (showTerm False) xs
      showTerm isLeading (Zero, _) = if isLeading then "0" else ""
      showTerm isLeading (Positive s, deg) = if isLeading then s ++ deg else " + " ++ s ++ deg
      showTerm isLeading (Negative s, deg) = if isLeading then '-' : s ++ deg else " - " ++ s ++ deg
      showTerm isLeading (Eps, deg) = if isLeading then deg else " + " ++ deg
      procTerm (getMonomial -> deg, c)
          | isZero c = Nothing
          | otherwise =
              let cKind = showCoeff c
                  cff | isConstantMonomial deg && isOne c      = Positive "1"
                      | isConstantMonomial deg && isMinusOne c = Negative "1"
                      | isOne c = Positive ""
                      | isMinusOne c = Negative ""
                      | otherwise                                 = cKind
              in Just $ (cff, unwords (mapMaybe showDeg (zip [1..] $ V.toList deg)))
      showDeg (n, p) | p == 0    = Nothing
                     | p == 1    = Just $ showVar n
                     | otherwise = Just $ showVar n ++ "^" ++ show p
      showVar n = fromMaybe ("X_" ++ show n) $ lookup n vDic

isConstantMonomial :: (Eq a, Num a) => Vector a n -> Bool
isConstantMonomial v = all (== 0) $ V.toList v

-- | We provide Num instance to use trivial injection R into R[X].
--   Do not use signum or abs.
instance (IsMonomialOrder order, IsPolynomial r n, Num r) => Num (OrderedPolynomial r order n) where
  (+) = (Numeric.Algebra.+)
  (*) = (Numeric.Algebra.*)
  fromInteger = injectCoeff . P.fromInteger
  signum f = if isZero f then zero else injectCoeff 1
  abs = id
  negate = ((P.negate 1 :: Integer) .*)

varX :: (IsPolynomial r n, IsOrder order, One :<= n) => OrderedPolynomial r order n
varX = polynomial $ M.singleton (OrderedMonomial $ fromList sing [1]) one

var :: (IsPolynomial r m, IsOrder order, S n :<= m) => SNat (S n) -> OrderedPolynomial r order m
var vIndex = polynomial $ M.singleton (OrderedMonomial $ fromList sing (buildIndex vIndex)) one

toPolynomial :: (IsOrder order, IsPolynomial r n) => (r, Monomial n) -> OrderedPolynomial r order n
toPolynomial (c, deg) = polynomial $ M.singleton (OrderedMonomial deg) c

polynomial :: (IsPolynomial r n, IsOrder order) => Map (OrderedMonomial order n) r -> OrderedPolynomial r order n
polynomial dic = normalize $ Polynomial dic

buildIndex :: SNat (S n) -> [Natural]
buildIndex (SS SZ) = [1]
buildIndex (SS (SS n))  = 0 : buildIndex (SS n)

leadingTerm :: (IsOrder order, IsPolynomial r n)
                => OrderedPolynomial r order n -> (r, Monomial n)
leadingTerm (Polynomial d) =
  case M.maxViewWithKey d of
    Just ((deg, c), _) -> (c, getMonomial deg)
    Nothing -> (zero, fromList sing [])

leadingMonomial :: (IsOrder order, IsPolynomial r n) => OrderedPolynomial r order n -> Monomial n
leadingMonomial = snd . leadingTerm

leadingOrderedMonomial :: (IsOrder order, IsPolynomial r n)
                       => OrderedPolynomial r order n -> OrderedMonomial order n
leadingOrderedMonomial = OrderedMonomial . leadingMonomial

leadingCoeff :: (IsOrder order, IsPolynomial r n) => OrderedPolynomial r order n -> r
leadingCoeff = fst . leadingTerm

divs :: Monomial n -> Monomial n -> Bool
xs `divs` ys = and $ V.toList $ V.zipWith (<=) xs ys

tryDiv :: (DecidableUnits r, Field r) => (r, Monomial n) -> (r, Monomial n) -> (r, Monomial n)
tryDiv (a, f) (b, g)
    | g `divs` f, Just inv <- recipUnit b = (a * inv, V.zipWithSame (P.-) f g)
    | otherwise  = error "cannot divide."

lcmMonomial :: Monomial n -> Monomial n -> Monomial n
lcmMonomial = V.zipWithSame max

subst :: (Module r a, Ring a, Ring r, SingRep n) => Vector a n -> OrderedPolynomial r order n -> a
subst assign poly = sum $ map (uncurry (.*) . second extractPower) $ getTerms poly
  where
    extractPower = V.foldr (*) one . V.zipWithSame pow assign

-- | Partially difference at (m+1)-th variable
diff :: forall n m ord r. (Ring r, SingRep n, IsMonomialOrder ord, SingRep m, (m :<<= n) ~ True)
     => SNat m -> OrderedPolynomial r ord (S n) -> OrderedPolynomial r ord (S n)
diff mthVar = unwrapped %~ M.mapKeysWith (+) (unwrapped %~ dropDegree)
                         . M.mapWithKey (\k c -> c * NA.fromIntegral (V.index mthVar (getMonomial k)))
                         . M.filterWithKey (\k -> const $ V.index mthVar (getMonomial k) > 0)
  where
    dropDegree = updateNth mthVar (max 0 . pred)

updateNth :: (m :<<= n) ~ True => SNat m -> (a -> a) -> Vector a (S n) -> Vector a (S n)
updateNth SZ     f (a :- as) = f a :- as
updateNth (SS n) f (a :- b :- bs) = a :- updateNth n f (b :- bs)
updateNth _      _ _              = bugInGHC

sPolynomial :: (DecidableUnits k, IsPolynomial k n, Field k, IsOrder order)
            => OrderedPolynomial k order n
            -> OrderedPolynomial k order n -> OrderedPolynomial k order n
sPolynomial f g =
    let h = (one, lcmMonomial (leadingMonomial f) (leadingMonomial g))
    in toPolynomial (h `tryDiv` leadingTerm f) * f - toPolynomial (h `tryDiv` leadingTerm g) * g

changeOrder :: (Eq (Monomial n), IsOrder o, IsOrder o',  SingRep n)
            => o' -> OrderedPolynomial k o n -> OrderedPolynomial k o' n
changeOrder _ = unwrapped %~ M.mapKeys (OrderedMonomial . getMonomial)

changeOrderProxy :: (Eq (Monomial n), IsOrder o, IsOrder o',  SingRep n)
            => Proxy o' -> OrderedPolynomial k o n -> OrderedPolynomial k o' n
changeOrderProxy _ = unwrapped %~ M.mapKeys (OrderedMonomial . getMonomial)

getTerms :: OrderedPolynomial k order n -> [(k, Monomial n)]
getTerms = map (snd &&& getMonomial . fst) . M.toDescList . terms

transformMonomial :: (IsOrder o, IsPolynomial k n, IsPolynomial k m)
                  => (Monomial n -> Monomial m) -> OrderedPolynomial k o n -> OrderedPolynomial k o m
transformMonomial trans (Polynomial d) = Polynomial $ M.mapKeys (OrderedMonomial . trans . getMonomial) d

orderedBy :: IsOrder o => OrderedPolynomial k o n -> o -> OrderedPolynomial k o n
p `orderedBy` _ = p

shiftR :: forall k r n ord. (Field r, IsPolynomial r n, IsPolynomial r (k :+: n), IsOrder ord)
       => SNat k -> OrderedPolynomial r ord n -> OrderedPolynomial r ord (k :+: n)
shiftR k =
  case singInstance k of
    SingInstance -> transformMonomial (V.append (fromList k []))

genVars :: forall k o n. (IsPolynomial k (S n), IsOrder o)
        => SNat (S n) -> [OrderedPolynomial k o (S n)]
genVars sn =
    let n  = sNatToInt sn
        seed = cycle $ 1 : replicate (n - 1) 0
    in map (\m -> Polynomial $ M.singleton (OrderedMonomial $ fromList sn $ take n (drop (n-m) seed)) one) [0..n-1]

sArity :: OrderedPolynomial k ord n -> SNat n
sArity (Polynomial dic) = V.sLength $ getMonomial $ fst $ M.findMin dic
{-# RULES
"sArity/zero" forall (v :: OrderedPolynomial k ord Z).                     sArity v = SZ
"sArity/one" forall (v :: OrderedPolynomial k ord (S Z)).                  sArity v = SS SZ
"sArity/two" forall (v :: OrderedPolynomial k ord (S (S Z))).              sArity v = SS (SS SZ)
"sArity/three" forall (v :: OrderedPolynomial k ord (S (S (S Z)))).        sArity v = SS (SS (sS SZ))
"sArity/four" forall (v :: OrderedPolynomial k ord (S (S (S (S Z))))).     sArity v = SS (SS (SS (SS SZ)))
"sArity/five" forall (v :: OrderedPolynomial k ord (S (S (S (S (S Z)))))). sArity v = SS (SS (SS (SS (SS SZ))))
"sArity/sing" forall (v :: SingRep n => OrderedPolynomial k ord n).           sArity (v :: OrderedPolynomial k ord n) = sing :: SNat n
  #-}
