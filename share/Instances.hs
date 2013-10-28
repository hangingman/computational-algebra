{-# LANGUAGE ConstraintKinds, DataKinds, DeriveGeneric, FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances, GADTs, GeneralizedNewtypeDeriving             #-}
{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances, ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving, UndecidableInstances                         #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
module Instances (ZeroDimIdeal(..), polyOfDim, arbitraryRational, forAllPolyOfDim
                 , quotOfDim, oldQuotOfDim, isNonTrivial, toOldPoly, fromOldPoly) where
import           Algebra.Ring.Noetherian
import           Algebra.Ring.Polynomial             hiding (Positive)
import           Algebra.Ring.Polynomial.Quotient
import qualified Algebra.Ring.Polynomial.QuotientOld as OP
import qualified Algebra.Ring.PolynomialOld          as OP
import           Control.Applicative
import           Control.Arrow
import           Control.Lens
import           Control.Monad
import qualified Data.Map                            as M
import           Data.Proxy
import           Data.Ratio
import           Data.Reflection                     hiding (Z)
import           Data.Type.Natural
import           Data.Vector.Sized                   (Vector (..))
import qualified Numeric.Algebra                     as NA
import           Test.QuickCheck
import qualified Test.QuickCheck                     as QC
import           Test.QuickCheck.Instances           ()
import           Test.SmallCheck.Series
import qualified Test.SmallCheck.Series              as SC

newtype ZeroDimIdeal n = ZeroDimIdeal { getIdeal :: Ideal (Polynomial Rational n)
                                      } deriving (Show, Eq, Ord)

(%.) :: Integral a => a -> SC.Positive a -> Ratio a
a %. SC.Positive b = a % b

-- * Instances for SmallCheck.
instance Monad m => Serial m NA.Natural where
  series = fromInteger . SC.getNonNegative <$> series

instance (Integral a, Ord a, Serial m a) => Serial m (Ratio a) where
  series = cons2 (%.)

instance (SingRep n, Serial m (Vector NA.Natural n)) => Serial m (Vector NA.Natural n) where
  series =
    case sing :: SNat n of
      SZ -> SC.cons0 Nil
      SS _ -> SC.cons2 (:-)

instance Serial m (Vector NA.Natural n) => Serial m (Monomial n) where
  series = newtypeCons fromVector

instance (Ord k, Serial m k, Serial m v) => Serial m (M.Map k v) where
  series = M.fromList <$> series

instance Serial m (Monomial n) => Serial m (OrderedMonomial ord n) where
  series = newtypeCons OrderedMonomial

instance (IsPolynomial r n, IsMonomialOrder ord, Serial m r, Serial m (Monomial n))
          => Serial m (OrderedPolynomial r ord n) where
  series = cons2 (curry toPolynomial) \/ cons2 (NA.+)

instance (Num r, Ord r, NA.DecidableZero r, NoetherianRing r, Serial m r) => Serial m (Ideal r) where
  series = newtypeCons toIdeal

forAllPolyOfDim :: Monad m => SNat n -> Series m (Polynomial Rational n)
forAllPolyOfDim n = case singInstance n of SingInstance ->  series

appendLM :: Rational -> Monomial Two -> Polynomial Rational Two -> Polynomial Rational Two
appendLM coef lm = unwrapped %~ M.insert (OrderedMonomial lm) coef

xPoly :: Monad m => SC.Series m (Polynomial Rational Two)
xPoly = do
  (series SC.>< series) >>- \(c, d) ->
    series >>- \p -> do
      guard $ OrderedMonomial (leadingMonomial p) < (OrderedMonomial (fromVector $ d :- 0 :- Nil) :: OrderedMonomial Grevlex Two)
      return $ appendLM c (fromVector $ d :- 0 :- Nil) p

yPoly :: Monad m => SC.Series m (Polynomial Rational Two)
yPoly = do
  (series SC.>< series) >>- \(c, d) ->
    series >>- \p -> do
      guard $ OrderedMonomial (leadingMonomial p) < (OrderedMonomial (fromVector $ d :- 0 :- Nil) :: OrderedMonomial Grevlex Two)
      return $ appendLM c (fromVector $ 0 :- d :- Nil) p

instance Monad m => Serial m (ZeroDimIdeal Two) where
  series = do
    (f, g, ideal) <- (,,) <$> xPoly <~> yPoly <~> series
    return $ ZeroDimIdeal $ f `addToIdeal` g `addToIdeal` ideal

-- * Instances for QuickCheck.
instance SingRep n => Arbitrary (Monomial n) where
  arbitrary = arbVec

arbVec :: forall n. SingRep n => Gen (Monomial n)
arbVec = fromList len <$> vector (sNatToInt len)
    where
      len = sing :: SNat n

instance Arbitrary NA.Natural where
  arbitrary = fromInteger . QC.getNonNegative <$> arbitrary

instance (IsOrder ord, Arbitrary (Monomial n)) => Arbitrary (OrderedMonomial ord n) where
  arbitrary = OrderedMonomial <$> arbitrary

instance (SingRep n, IsOrder ord)
      => Arbitrary (OrderedPolynomial Rational ord n) where
  arbitrary = polynomial . M.fromList <$> listOf1 ((,) <$> arbitrary <*> arbitraryRational)

instance (Ord r, NA.DecidableZero r, NoetherianRing r, Arbitrary r, Num r) => Arbitrary (Ideal r) where
  arbitrary = toIdeal . getNonEmpty <$> arbitrary

instance (SingRep n) => Arbitrary (ZeroDimIdeal n) where
  arbitrary = zeroDimG

instance (NA.Field r, NA.DecidableUnits r, NA.DecidableZero r, NoetherianRing r, Reifies ideal (QIdeal r ord n)
         , Arbitrary (OrderedPolynomial r ord n)
         , IsMonomialOrder ord, SingRep n, Eq r)
    => Arbitrary (Quotient r ord n ideal) where
  arbitrary = modIdeal <$> arbitrary

instance (Reifies ideal (OP.QIdeal Rational OP.Grevlex n)
         , SingRep n)
    => Arbitrary (OP.Quotient Rational OP.Grevlex n ideal) where
  arbitrary = OP.modIdeal . toOldPoly <$> arbitrary

polyOfDim :: SingRep n => SNat n -> QC.Gen (Polynomial Rational n)
polyOfDim _ = arbitrary

quotOfDim :: (SingRep n, Reifies ideal (QIdeal Rational Grevlex n))
          => Proxy ideal -> QC.Gen (Quotient Rational Grevlex n ideal)
quotOfDim _ = arbitrary

oldQuotOfDim :: (SingRep n, Reifies ideal (OP.QIdeal Rational OP.Grevlex n))
          => Proxy ideal -> QC.Gen (OP.Quotient Rational OP.Grevlex n ideal)
oldQuotOfDim _ = arbitrary

genLM :: forall n. SNat n -> QC.Gen [Polynomial Rational n]
genLM SZ = return []
genLM (SS n) = do
  fs <- map (shiftR sOne) <$> genLM n
  deg <- arbitrary
  coef <- arbitraryRational `suchThat` (/= 0)
  xf <- arbitrary :: QC.Gen (Polynomial Rational n)
  let xlm = OrderedMonomial $ fromList (sS n) [deg + 1]
      f = xf & unwrapped %~ M.insert xlm coef . M.filterWithKey (\k _ -> k < xlm)
  return $ f : fs

zeroDimG :: forall n. (SingRep n) => QC.Gen (ZeroDimIdeal n)
zeroDimG = do
  fs <- genLM (sing :: SNat n)
  i0 <- arbitrary
  return $ ZeroDimIdeal $ toIdeal $ fs ++ i0

arbitraryRational :: QC.Gen Rational
arbitraryRational = do
  a <- QC.arbitrarySizedIntegral
  b <- QC.arbitrarySizedIntegral `suchThat` \b -> b > 0 && gcd a b == 1
  return $ a % b

isNonTrivial :: SingRep n => ZeroDimIdeal n -> Bool
isNonTrivial (ZeroDimIdeal ideal) = reifyQuotient ideal $ maybe False ((>0).length) . standardMonomials'

toOldPoly :: SingRep n => Polynomial Rational n -> OP.Polynomial Rational n
toOldPoly poly = OP.polynomial $ M.fromListWith (+) $ map ((OP.OrderedMonomial . degree . snd) &&& fst) $ getTerms poly

fromOldPoly :: SingRep n => OP.Polynomial Rational n -> Polynomial Rational n
fromOldPoly opoly = polynomial $ M.fromListWith (+) $
                    map ((OrderedMonomial . fromVector . snd ) &&& fst) $ OP.getTerms opoly
