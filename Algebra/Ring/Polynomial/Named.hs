{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts             #-}
{-# LANGUAGE FlexibleInstances, GADTs, GeneralizedNewtypeDeriving     #-}
{-# LANGUAGE KindSignatures, MultiParamTypeClasses, NoImplicitPrelude #-}
{-# LANGUAGE PolyKinds, ScopedTypeVariables, StandaloneDeriving       #-}
{-# LANGUAGE TemplateHaskell, TypeFamilies, TypeOperators             #-}
{-# LANGUAGE UndecidableInstances                                     #-}
module Algebra.Ring.Polynomial.Named where
import Algebra.Prelude
import Algebra.Algorithms.Groebner
import Control.Lens                (makeWrapped)
import Data.Type.Natural           (Nat (..), SNat, Sing (SS, SZ))
import Numeric.Semiring.Integral   (IntegralSemiring)
import Prelude (Num)
import Data.Singletons.Prelude
import Data.Vector.Sized ((%!!))
import GHC.TypeLits hiding (Nat)
import qualified GHC.TypeLits as TL
import Data.Singletons.TH (genDefunSymbols)
import Data.Singletons.Decide
import Unsafe.Coerce (unsafeCoerce)
import GHC.Exts (Constraint)
import qualified Data.Vector.Sized as V
import qualified Prelude as P
import Data.Singletons.TH (singletons)
import Data.Type.Natural (natToInt)
import Data.Type.Natural ((:+), (%:+), plusSR)
import Proof.Equational ((:=:))
import Proof.Equational (start)
import Proof.Equational (admitted)
import Proof.Equational ((===), (=~=))
import Proof.Equational (cong')
import Proof.Equational (because)
import Data.Singletons.Types (Proxy(..))
import Proof.Equational (cong)

type family Len (vs :: [k]) :: Nat where
  Len '[] = Z
  Len (x ': xs) = S (Len xs)

sLen :: SList (vs :: [k]) -> SNat (Len vs)
sLen SNil = SZ
sLen (SCons _ xs) = SS $ sLen xs

newtype QPolynomial r ord (vs :: [Symbol]) =
  QPolynomial { runQPolynomial :: OrderedPolynomial r ord (Len vs) }

makeWrapped ''QPolynomial

deriving instance (IsOrder ord, SingI (Len vs), DecidableZero r, Ring r, Eq r)
               => Eq (QPolynomial r ord vs)

deriving instance (Ord r, IsOrder ord, SingI (Len vs), DecidableZero r, Ring r, Eq r)
               => Ord (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Len vs), Ring r)
               => Additive (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Len vs), Ring r)
               => Multiplicative (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Len vs), Ring r)
               => Abelian (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Len vs), Ring r)
               => LeftModule Natural (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Len vs), Ring r)
               => RightModule Natural (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Len vs), Ring r)
               => LeftModule Integer (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Len vs), Ring r)
               => RightModule Integer (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Len vs), Ring r)
               => Monoidal (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Len vs), Ring r)
               => Group (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Len vs), Ring r)
               => Commutative (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Len vs), Ring r)
               => Semiring (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Len vs), Ring r)
               => Unital (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Len vs), Ring r)
               => Rig (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Len vs), Ring r)
               => Ring (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, DecidableUnits r,
                   SingI (Len vs), Ring r)
               => DecidableUnits (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Len vs), Ring r)
               => DecidableZero (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, Ring r,
                   SingI (Len vs), IntegralSemiring r)
               => IntegralSemiring  (QPolynomial r ord vs)

deriving instance (IsMonomialOrder ord, IntegralSemiring r,
                   Commutative r, Field r, DecidableZero r,
                   Eq r, DecidableUnits r)
               => Euclidean (QPolynomial r ord '[v])

instance (IsOrder ord, DecidableZero r, SingI (Len vs), SingI vs, Ring r, Show r)
      => Show (QPolynomial r ord vs) where
  show f = showPolynomialWithVars (zip [0..] $ buildVars f) (runQPolynomial f)

deriving instance (IsMonomialOrder order, Ring r, DecidableZero r, SingI (Len vs), Num r)
               => Num (QPolynomial r order vs)
  
buildVars :: forall proxy (vs :: [Symbol]). SingI vs => proxy vs -> [String]
buildVars _ = fromSing (sing :: SList vs)
{-# INLINE buildVars #-}

withVars :: proxy vs -> OrderedPolynomial r ord (Len vs) -> QPolynomial r ord vs
withVars _ = QPolynomial
{-# INLINE withVars #-}

genVarsFor :: forall r ord vs. (IsOrder ord, SingI (Len vs),
                                 DecidableZero r,Ring r)
           => Sing vs -> [QPolynomial r ord vs]
genVarsFor vs = map QPolynomial $ genVars $ sLen vs

type family FindIndex xs x where
  FindIndex '[]       x = Nothing
  FindIndex (x ': xs) x = Just Z
  FindIndex (y ': xs) x = RecFindInd (FindIndex xs x)

type family RecFindInd (m :: Maybe Nat) :: Maybe Nat
type instance RecFindInd Nothing  = Nothing
type instance RecFindInd (Just n) = Just (S n)

genDefunSymbols [''FindIndex, ''RecFindInd]

type Permute xs ys = Map (Apply FindIndexSym0 xs) ys

sPermute :: SDecide ('KProxy :: KProxy k)
         => SList (xs :: [k]) -> SList ys -> SList (Permute xs ys)
sPermute _ SNil = SNil
sPermute xs (SCons y ys) = SCons (sFindIndex xs y) $ sPermute xs ys

sFindIndex :: SDecide ('KProxy :: KProxy k)
           => SList xs -> Sing (x :: k) -> SMaybe (FindIndex xs x)
sFindIndex SNil         _ = SNothing
sFindIndex (SCons x xs) y =
  case x %~ y of
    Proved Refl -> SJust SZ
    Disproved _ -> unsafeCoerce $  sRecFindInd (sFindIndex xs y)

sRecFindInd :: SMaybe n -> SMaybe (RecFindInd n)
sRecFindInd SNothing  = SNothing
sRecFindInd (SJust n) = SJust (SS n)

type family BelongsTo xs x :: Constraint where
   BelongsTo (x ': xs) x = ()
   BelongsTo (y ': ys) x = BelongsTo ys x

type family AllC (p :: k -> Constraint) (xs :: [k]) :: Constraint where
  AllC p '[] = ()
  AllC p (x ': xs) = (p x, AllC p xs)

unsafeInjection :: forall pxy vs vs' r ord.
                    (SingI (Len vs'), SingI (Len vs), SingI (Permute vs vs'),
                     IsOrder ord, DecidableZero r, Ring r)
                 => pxy vs' -> QPolynomial r ord vs -> QPolynomial r ord vs'
unsafeInjection _ (QPolynomial f) =
  let ids = fromSing (sing :: SList (Permute vs vs'))
      build m = V.unsafeFromList' $ map (maybe 0 ((m %!!) . P.fromInteger . natToInt)) ids
  in QPolynomial $ transformMonomial build f

injection :: forall pxy vs vs' r ord.
                    (SingI (Len vs'), SingI (Len vs), SingI (Permute vs vs'),
                     All (FlipSym0 @@ ElemSym0 @@ vs') vs ~ True,
                     IsOrder ord, DecidableZero r, Ring r)
                 => pxy vs' -> QPolynomial r ord vs -> QPolynomial r ord vs'
injection = unsafeInjection

singletons [d|
  partition :: (a -> Bool) -> [a] -> ([a], [a])
  partition _ [] = ([], [])
  partition p (x : xs) = case partition p xs of
              (ys,ns) -> if p x then (x:ys, ns) else (ys, x:ns)
 |]

lenDistr :: SList xs -> SList ys -> Len (xs :++ ys) :=: Len xs :+ Len ys
lenDistr SNil _ = Refl
lenDistr (SCons x xs) ys =
  start (sLen $ SCons x xs %:++ ys)
    =~= sLen (SCons x (xs %:++ ys))
    =~= SS (sLen (xs %:++ ys))
    === SS (sLen xs %:+ sLen ys)       `because` cong' SS (lenDistr xs ys)
    =~= SS (sLen xs) %:+ sLen ys
    =~= sLen (SCons x xs) %:+ sLen ys

partitionLength :: (Partition p xs ~ '(ls, rs))
                => Sing p -> SList xs -> Len xs :=: Len ls :+ Len rs
partitionLength _ SNil = Refl
partitionLength p (SCons x xs) =
  case sPartition p xs of
    STuple2 ls rs -> case applySing p x of
      STrue -> start (sLen (SCons x xs))
                  =~= SS (sLen xs)
                  === SS (sLen ls %:+ sLen rs)
                        `because` cong' SS (partitionLength p xs)
                  =~= SS (sLen ls) %:+ sLen rs
                  =~= sLen (SCons x ls) %:+ sLen rs
      SFalse -> start (sLen (SCons x xs))
                  =~= SS (sLen xs)
                  === SS (sLen ls %:+ sLen rs)
                        `because` cong' SS (partitionLength p xs)
                  === sLen ls %:+ SS (sLen rs)
                        `because` plusSR (sLen ls) (sLen rs)
                  =~= sLen ls %:+ sLen (SCons x rs)

belongsTo :: forall xs. SEq ('KProxy :: KProxy k) => SList (xs :: [k]) -> Sing ((FlipSym0 @@ ElemSym0) @@ xs)
belongsTo zs = singFun1 (Proxy :: Proxy (FlipSym0 @@ ElemSym0 @@ xs)) (flip sElem zs)

eliminate :: forall r ord vs. (IsMonomialOrder ord, DecidableZero r, Eq r, Field r, SingI vs)
          => [String] -> Ideal (QPolynomial r ord vs) -> Ideal (QPolynomial r ord vs)
eliminate dels0 ideal =
  let vs = sing :: SList vs
  in case toSing dels0 :: SomeSing ('KProxy :: KProxy [Symbol])of
    SomeSing (dels :: SList targs) ->
      case sPartition (belongsTo dels) vs of
        STuple2 (ds :: SList ds) (ns :: SList ns) ->
          case lenDistr ds ns of
            Refl ->
             case partitionLength (belongsTo dels) vs of
               Refl ->
                 let reorded = ds %:++ ns in
                 withSingI (sLen ds) $ withSingI (sLen ns) $ withSingI (sLen ds %:+ sLen ns ) $
                 withSingI (sMap (singFun1 (Proxy :: Proxy (FindIndexSym1 vs)) $ sFindIndex vs) reorded) $ 
                 withSingI (sMap (singFun1 (Proxy :: Proxy (FindIndexSym1 (ds :++ ns))) $ sFindIndex reorded) vs) $ 
                 toIdeal $ map (unsafeInjection vs . withVars reorded . changeOrderProxy Proxy) $
                 filter (\f -> all (V.all (== 0) . V.takeAtMost (sLen ds) . getMonomial) $ monomials f) $ 
                 calcGroebnerBasisWith (weightedEliminationOrder (sLen ds)) $
                 mapIdeal (runQPolynomial . unsafeInjection (ds %:++ ns)) ideal
