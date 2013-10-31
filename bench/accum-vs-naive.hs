{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs            #-}
{-# LANGUAGE MultiParamTypeClasses, OverloadedStrings, PolyKinds, QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell, UndecidableInstances                            #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
import qualified Algebra.Algorithms.Groebner    as P
import qualified Algebra.Algorithms.GroebnerOld as OP
import           Algebra.Ring.Noetherian
import qualified Algebra.Ring.Polynomial        as P
import qualified Algebra.Ring.PolynomialOld     as OP
import           Control.DeepSeq
import           Control.Lens
import           Control.Parallel.Strategies
import           Criterion
import           Data.Type.Natural
import           Instances
import           Progression.Main
import           System.Environment

type Polyn = P.Polynomial Rational Eight

x, y, z, w, s, a, b, c :: Polyn
[x, y, z, w, s, a, b, c] = P.genVars sEight

i1, i2, i3, i4 :: Ideal Polyn
i1 = toIdeal [x^2 + y^2 + z^2 - 1, x^2 + y^2 + z^2 - 2*x, 2*x -3*y - z]
i2 = toIdeal [x^2 * y - 2*x*y - 4*z - 1, z-y^2, x^3 - 4*z*y]
i3 = toIdeal [ 2 * s - a * y, b^2 - (x^2 + y^2), c^2 - ( (a-x) ^ 2 + y^2)
             ]
i4 = toIdeal [ z^5 + y^4 + x^3 - 1, z^3 + y^3 + x^2 - 1]

main :: IO ()
main = do
  ideal1 <- return $! TestIdeal (i1 `using` rdeepseq) (mapIdeal toOldPoly i1 `using` rdeepseq)
  idealLex1 <- return $! TestIdeal (mapIdeal (P.changeOrder P.Lex) i1 `using` rdeepseq)
                           ((mapIdeal (OP.changeOrder OP.Lex . toOldPoly) i1) `using` rdeepseq)
  idealGrlex1 <- return $! TestIdeal (mapIdeal (P.changeOrder P.Grlex) i1 `using` rdeepseq)
                            (mapIdeal (OP.changeOrder OP.Grlex . toOldPoly) i1 `using` rdeepseq)
  ideal2 <- return $! TestIdeal (i2 `using` rdeepseq)
                       ((mapIdeal toOldPoly i2) `using` rdeepseq)
  idealGrlex2 <- return $! TestIdeal (mapIdeal (P.changeOrder P.Grlex) i2 `using` rdeepseq)
                            (mapIdeal (OP.changeOrder OP.Grlex . toOldPoly) i2 `using` rdeepseq)
  ideal3 <- return $! TestIdeal (i3 `using` rdeepseq)
                       ((mapIdeal toOldPoly i3) `using` rdeepseq)
  idealLex3 <- return $! TestIdeal (mapIdeal (P.changeOrder P.Lex) i3 `using` rdeepseq)
                          ((mapIdeal (OP.changeOrder OP.Lex . toOldPoly) i3) `using` rdeepseq)
  idealGrlex3 <- return $! TestIdeal (mapIdeal (P.changeOrder P.Grlex) i3 `using` rdeepseq)
                            (mapIdeal (OP.changeOrder OP.Grlex . toOldPoly) i3 `using` rdeepseq)
  ideal4 <- return $! TestIdeal (i4 `using` rdeepseq)
                       ((mapIdeal toOldPoly i4) `using` rdeepseq)
  idealGrlex4 <- return $! TestIdeal (mapIdeal (P.changeOrder P.Grlex) i4 `using` rdeepseq)
                            (mapIdeal (OP.changeOrder OP.Grlex . toOldPoly) i4 `using` rdeepseq)
  args <- getArgs
  let toBench :: (P.IsMonomialOrder ord, ToOld ord, OP.IsMonomialOrder (Old ord))
              => String -> TestIdeal (P.OrderedPolynomial Rational ord Eight) -> Benchmark
      toBench name =
          case args of
            "old":_ -> bench name . nf OP.calcGroebnerBasis . oldIdeal
            "acc":_ -> bench name . nf P.calcGroebnerBasis . newIdeal
            _ -> error "kanasimi"
  withArgs (args &_head %~ ("-n"++)) $ do
         defaultMain $ bgroup "calcGroebner"
                  [bgroup "case01"
                              [ toBench "lex" idealLex1
                              , toBench "grlex" idealGrlex1
                              , toBench "grevlex" ideal1
                              ]
                  , bgroup "case02"
                               [ toBench "grlex" idealGrlex2
                               , toBench "grevlex" ideal2
                               ]
                  , bgroup "case03"
                               [ toBench "lex" idealLex3
                               , toBench "grlex" idealGrlex3
                               , toBench "grevlex" ideal3
                               ]
                  , bgroup "case04"
                               [ toBench "grlex" idealGrlex4
                               , toBench "grevlex" ideal4
                               ]
                  ]

