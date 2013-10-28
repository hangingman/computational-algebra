{-# LANGUAGE ExistentialQuantification, ImpredicativeTypes, RankNTypes #-}
module Main where
import qualified Algebra.Ring.Polynomial     as P
import           Control.Applicative
import           Control.DeepSeq
import           Control.Monad
import           Control.Parallel.Strategies
import           Criterion.Main
import           Data.Type.Monomorphic
import qualified SequenceMonomial            as S
import           System.Random
import           Test.QuickCheck

data MonomPair = forall n. MonomPair { getMonoms :: !(P.Monomial n, P.Monomial n) }

instance NFData MonomPair where
  rnf (MonomPair (n, m)) = rnf n `seq` rnf m `seq` ()

main :: IO ()
main = do
  as0 <- replicateM 5 genMonomial
  as <- return $!! (as0 `using` rdeepseq)
  defaultMain $ zipWith mkTestCase [1..] as

genMonomial :: IO (MonomPair, (S.Monomial, S.Monomial))
genMonomial = do
  len <- abs <$> randomRIO (5, 20)
  liftM head . sample' $ do
    m <- map abs <$> vector len
    n <- map abs <$> vector len
    let mp = withPolymorhic len $ \sn -> MonomPair (P.fromList sn m, P.fromList sn n)
    return (mp, (S.fromList m, S.fromList n))

instance NFData Ordering where
  rnf EQ = ()
  rnf LT = ()
  rnf GT = ()

mkTestCase :: Int -> (MonomPair, (S.Monomial, S.Monomial)) -> Benchmark
mkTestCase n (MonomPair m, m') =
    bgroup ("case-" ++ show n ++ "-len" ++ show len) $
           map subcase
                   [ ("lex", P.lex, S.lex)
                   , ("revlex", P.revlex, S.revlex)
                   , ("grlex", P.grlex, S.grlex)
                   , ("grevlex", P.grevlex, S.grevlex)
                   ]
  where
    len = S.length $ fst m'
    subcase :: (String, P.MonomialOrder, S.MonomialOrder) -> Benchmark
    subcase (name, pol, sq) =
        bgroup name [ bench "vector" $ nf (uncurry pol) m
                    , bench "sequence" $ nf (uncurry sq) m'
                    ]
