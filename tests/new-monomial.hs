{-# LANGUAGE DataKinds, PolyKinds, RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE TupleSections, ViewPatterns                           #-}
module Main where
import qualified Algebra.Algorithms.Groebner         as P
import qualified Algebra.Algorithms.GroebnerOld      as OP
import qualified Algebra.Ring.Polynomial             as P
import qualified Algebra.Ring.Polynomial.Monomorphic as MP
import qualified Algebra.Ring.PolynomialOld          as OP
import           Control.Arrow
import           Control.Lens
import           Data.Function
import           Data.Type.Monomorphic
import           Data.Type.Natural                   hiding (max, min)
import           Data.Vector.Sized                   (Vector (..))
import qualified Data.Vector.Sized                   as V
import           Instances
import qualified Numeric.Algebra                     as NA
import           Numeric.Decidable.Zero
import           Test.Hspec
import qualified Test.Hspec.QuickCheck               as QC
import qualified Test.Hspec.SmallCheck               as SC
import qualified Test.QuickCheck                     as QC
import qualified Test.SmallCheck                     as SC
import qualified Test.SmallCheck.Series              as SC

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "withLen" $ do
    it "preserves elements" $ QC.forAll QC.arbitrary $ \xs ->
        let ps = withPolymorhic xs $ \vec -> V.toList $ P.withLen vec
        in map fst ps == xs
    it "counts subsum" $ QC.forAll QC.arbitrary $ \xs ->
        let ps = withPolymorhic xs $ \vec -> V.toList $ P.withLen vec
        in ps == zip xs (init $ scanr (+) 0 xs)
  describe "Monomial orderings" $ do
    coincidesOnTwoMonom "lex" P.lex OP.lex
    coincidesOnTwoMonom "revlex" P.revlex OP.revlex
    coincidesOnTwoMonom "grlex" P.grlex OP.grlex
    coincidesOnTwoMonom "grevlex" P.grevlex OP.grevlex
  describe "Total degree" $ do
    it "keeps non-negative after operation (new)" $ QC.property $
      QC.forAll (polyOfDim sTwo) $ \f -> QC.forAll (polyOfDim sTwo) $ \g ->
        P.totalDegree' (f * g) >= 0 && P.totalDegree' (f + g) >= 0 && P.totalDegree' (f - g) >= 0
    it "keeps non-negative after operation (old)" $ QC.property $
      QC.forAll (polyOfDim sTwo) $ \(toOldPoly -> f) -> QC.forAll (polyOfDim sTwo) $ \(toOldPoly -> g) ->
        OP.totalDegree' (f * g) >= 0 && OP.totalDegree' (f + g) >= 0 && OP.totalDegree' (f - g) >= 0
    it "keeps correct after operation (new)" $ QC.property $
      QC.forAll (polyOfDim sTwo) $ \f -> QC.forAll (polyOfDim sTwo) $ \g ->
        let cmp = all (\m -> P.totalDegree m == V.sum (P.degree m)) . map snd . P.getTerms
        in all cmp $ [f * g, f - g, f + g] ++ [P.sPolynomial f g | not (isZero f), not (isZero g)] ++
                     [P.modPolynomial f [g] | not $ isZero g]
    coincidesOnTwoPolyn "after operation" sThree totOpP totOpOP
  describe "New impelemtation" $ do
    coincidesOnTwoMonom "compare" compare compare
    coincidesOnTwoPolyn "multiplication" sThree multP multOP
    coincidesOnTwoMonom "divs" P.divs OP.divs
    coincidesOnTwoMonom "tryDiv" divP divOP
    coincidesOnTwoMonom "lcmMonomial" (((demote' . P.degree) . ) . P.lcmMonomial) ((demote' .) . OP.lcmMonomial)
    coincidesOnOneMonom "totalDegree" P.totalDegree OP.totalDegree
    coincidesOnOnePolyn "totalDegree'" sThree P.totalDegree' OP.totalDegree'
    coincidesOnOnePolyn "leadingMonomial" sThree lmP lmOP
    coincidesOnTwoPolyn "sPolynomial" sThree sPolyP sPolyOP
    coincidesOnTwoPolyn "divModPolynomial" sThree divModPolynomialP divModPolynomialOP

coincidesOnTwoMonom :: Eq a => String
            -> (forall n. P.Monomial n -> P.Monomial n -> a)
            -> (forall n. OP.Monomial n -> OP.Monomial n -> a)
            -> Spec
coincidesOnTwoMonom label p old = do
  QC.prop ("coincides on " ++ label ++ " (random)") $ compMonomQC p old
  it ("coincides on " ++ label ++ " (exhaustive)") $ SC.property $ compMonomSC p old

coincidesOnOneMonom :: Eq a => String
            -> (forall n. P.Monomial n -> a)
            -> (forall n. OP.Monomial n -> a)
            -> Spec
coincidesOnOneMonom label p old = do
  QC.prop ("coincides on " ++ label ++ " (random)") $ compMonomQC1 p old
  it ("coincides on " ++ label ++ " (exhaustive)") $ SC.property $ compMonomSC1 p old

coincidesOnOnePolyn :: Eq a
                    => String -> SNat n
                    -> (P.Polynomial Rational n -> a)
                    -> (OP.Polynomial Rational n -> a)
                    -> Spec
coincidesOnOnePolyn label dim p old = do
  QC.prop ("coincides on " ++ label ++ " (random)") $ compPolyQC1 dim p old
  it ("coincides on " ++ label ++ " (exhaustive)") $ SC.property $ compPolySC1 dim p old

coincidesOnTwoPolyn :: Eq a => String -> SNat n
            -> (P.Polynomial Rational n -> P.Polynomial Rational n -> a)
            -> (OP.Polynomial Rational n -> OP.Polynomial Rational n -> a)
            -> Spec
coincidesOnTwoPolyn label dim p old = do
  QC.prop ("coincides on " ++ label ++ " (random)") $ compPolyQC dim p old
  it ("coincides on " ++ label ++ " (exhaustive)") $ SC.property $ compPolySC dim p old


divModPolynomialOP :: OP.Polynomial Rational n -> OP.Polynomial Rational n
                   -> Maybe ([(MP.Polynomial Rational, MP.Polynomial Rational)], MP.Polynomial Rational)
divModPolynomialOP f g =
  case singInstance (OP.sArity g) of
    SingInstance ->
        if isZero g
        then Nothing
        else Just $ f `OP.divModPolynomial` [g]
                       & _1.each.both %~ MP.polyn . demote' . fromOldPoly
                       & _2 %~ MP.polyn . demote' . fromOldPoly

divModPolynomialP :: P.Polynomial Rational n -> P.Polynomial Rational n
                  -> Maybe ([(MP.Polynomial Rational, MP.Polynomial Rational)], MP.Polynomial Rational)
divModPolynomialP f g =
    case singInstance (P.sArity f) of
      SingInstance ->
          if isZero g
          then Nothing
          else Just $ f `P.divModPolynomial` [g]
                         & _1.each.both %~ MP.polyn . demote'
                         & _2 %~ MP.polyn . demote'

sPolyOP :: OP.Polynomial Rational n -> OP.Polynomial Rational n
        -> Maybe (MP.Polynomial Rational)
sPolyOP f g =
    case singInstance (OP.sArity f) of
      SingInstance ->
          if isZero f || isZero g
          then Nothing
          else Just $ MP.polyn . demote' . fromOldPoly $ OP.sPolynomial f g

sPolyP :: P.Polynomial Rational n -> P.Polynomial Rational n
       -> Maybe (MP.Polynomial Rational)
sPolyP f g =
    case singInstance (P.sArity f) of
      SingInstance ->
          if isZero f || isZero g
          then Nothing
          else Just $ MP.polyn . demote' $ P.sPolynomial f g

multOP :: OP.Polynomial Rational n -> OP.Polynomial Rational n
        -> MP.Polynomial Rational
multOP f g =
    case singInstance (OP.sArity f) of
      SingInstance -> MP.polyn . demote' . fromOldPoly $  f * g

multP :: P.Polynomial Rational n -> P.Polynomial Rational n
       -> MP.Polynomial Rational
multP f g =
    case singInstance (P.sArity f) of
      SingInstance -> MP.polyn . demote' $ f * g

totOpOP :: OP.Polynomial Rational n -> OP.Polynomial Rational n
        -> (NA.Natural, NA.Natural, NA.Natural)
totOpOP f g =
    case singInstance (OP.sArity f) of
      SingInstance -> (f * g, f + g, f - g) & each %~ OP.totalDegree'

totOpP :: P.Polynomial Rational n -> P.Polynomial Rational n
       -> (NA.Natural, NA.Natural, NA.Natural)
totOpP f g =
    case singInstance (P.sArity f) of
      SingInstance -> (f * g, f + g, f - g) & each %~ P.totalDegree'

lmP :: P.Polynomial Rational a -> [NA.Natural]
lmP f =
  case singInstance (P.sArity f) of
    SingInstance -> demote' . P.degree . P.leadingMonomial $ f

lmOP :: OP.Polynomial Rational a -> [NA.Natural]
lmOP f =
    case singInstance (OP.sArity f) of
      SingInstance -> demote' . OP.leadingMonomial $ f


divP :: P.Monomial n -> P.Monomial n -> Maybe (Rational, [NA.Natural])
divP f g | g `P.divs` f = Just $ second (V.toList . P.degree) $ (1 :: Rational, f) `P.tryDiv` (1 :: Rational, g)
         | otherwise    = Nothing

divOP :: OP.Monomial n -> OP.Monomial n -> Maybe (Rational, [NA.Natural])
divOP f g | g `OP.divs` f = Just $ second V.toList $
                            (1 :: Rational, f) `OP.tryDiv` (1 :: Rational, g)
          | otherwise     = Nothing

compMonomQC :: Eq a
       => (forall n. P.Monomial n -> P.Monomial n -> a)
       -> (forall n. OP.Monomial n -> OP.Monomial n -> a)
       -> QC.Property
compMonomQC pol sq =
    QC.forAll (QC.listOf $ QC.resize 7 QC.arbitrary) $ \m1 ->
           QC.forAll (QC.listOf $ QC.resize 7 QC.arbitrary) $ \m2 ->
             let len = max (length m1) (length m2)
             in withPolymorhic len $ \sn ->
                 pol (P.fromList sn m1) (P.fromList sn m2) == sq (OP.fromList sn m1) (OP.fromList sn m2)

compMonomQC1 :: Eq a
       => (forall n. P.Monomial n -> a)
       -> (forall n. OP.Monomial n -> a)
       -> QC.Property
compMonomQC1 pol sq =
    QC.forAll (QC.listOf $ QC.resize 7 QC.arbitrary) $ \m1 ->
        withPolymorhic (length m1) $ \sn ->
            pol (P.fromList sn m1) == sq (OP.fromList sn m1)

compPolyQC :: Eq a
       => SNat n
       -> (P.Polynomial Rational n -> P.Polynomial Rational n -> a)
       -> (OP.Polynomial Rational n -> OP.Polynomial Rational n -> a)
       -> QC.Property
compPolyQC dim pol sq =
  case singInstance dim of
    SingInstance ->
        QC.forAll (polyOfDim dim) $ \g -> QC.forAll (polyOfDim dim) $ \f ->
          pol f g == sq (toOldPoly f) (toOldPoly g)

compPolySC :: (Eq a, Monad m)
       => SNat n
       -> (P.Polynomial Rational n -> P.Polynomial Rational n -> a)
       -> (OP.Polynomial Rational n -> OP.Polynomial Rational n -> a)
       -> SC.Property m
compPolySC dim pol sq =
  case singInstance dim of
    SingInstance ->
        SC.over (forAllPolyOfDim dim) $ \g -> SC.over (forAllPolyOfDim dim) $ \f ->
          pol f g == sq (toOldPoly f) (toOldPoly g)

compPolyQC1 :: Eq a
       => SNat n
       -> (P.Polynomial Rational n -> a)
       -> (OP.Polynomial Rational n -> a)
       -> QC.Property
compPolyQC1 dim pol sq =
  case singInstance dim of
    SingInstance -> QC.forAll (QC.resize 5 $ polyOfDim dim) $ \f -> pol f == sq (toOldPoly f)

compPolySC1 :: forall n m a. (Monad m, Eq a)
            => SNat n
            -> (P.Polynomial Rational n -> a)
            -> (OP.Polynomial Rational n -> a)
            -> SC.Property m
compPolySC1 dim pol sq =
    case singInstance dim of
      SingInstance -> SC.over (forAllPolyOfDim dim) $ \f -> pol f == sq (toOldPoly f)

compMonomSC :: (Eq a, Monad m)
       => (forall n. P.Monomial n -> P.Monomial n -> a)
       -> (forall n. OP.Monomial n -> OP.Monomial n -> a)
       -> SC.Property m
compMonomSC pol sq =
    SC.forAll $ \m1 m2 ->
        let len = max (length m1) (length m2)
        in withPolymorhic len $ \sn ->
            pol (P.fromList sn m1) (P.fromList sn m2) == sq (OP.fromList sn m1) (OP.fromList sn m2)

compMonomSC1 :: (Eq a, Monad m)
       => (forall n. P.Monomial n -> a)
       -> (forall n. OP.Monomial n -> a)
       -> SC.Property m
compMonomSC1 pol sq =
    SC.forAll $ \m1 ->
        withPolymorhic (length m1) $ \sn ->
          pol (P.fromList sn m1) == sq (OP.fromList sn m1)

