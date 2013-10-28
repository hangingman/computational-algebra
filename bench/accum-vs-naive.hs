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
import           Control.Parallel.Strategies
import           Criterion.Main
import           Data.Type.Natural
import           Instances

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
  ideal1 <- return $! (i1 `using` rdeepseq)
  ideal1' <- return $! ((mapIdeal toOldPoly ideal1) `using` rdeepseq)
  idealLex1 <- return $! (mapIdeal (P.changeOrder P.Lex) i1 `using` rdeepseq)
  idealLex1' <- return $! ((mapIdeal (OP.changeOrder OP.Lex . toOldPoly) i1) `using` rdeepseq)
  idealGrlex1 <- return $! (mapIdeal (P.changeOrder P.Grlex) i1 `using` rdeepseq)
  idealGrlex1' <- return $! (mapIdeal (OP.changeOrder OP.Grlex . toOldPoly) i1 `using` rdeepseq)
  ideal2 <- return $! (i2 `using` rdeepseq)
  ideal2' <- return $! ((mapIdeal toOldPoly ideal2) `using` rdeepseq)
  idealGrlex2 <- return $! (mapIdeal (P.changeOrder P.Grlex) i2 `using` rdeepseq)
  idealGrlex2' <- return $! (mapIdeal (OP.changeOrder OP.Grlex . toOldPoly) i2 `using` rdeepseq)
  ideal3 <- return $! (i3 `using` rdeepseq)
  ideal3' <- return $! ((mapIdeal toOldPoly ideal3) `using` rdeepseq)
  idealLex3 <- return $! (mapIdeal (P.changeOrder P.Lex) i3 `using` rdeepseq)
  idealLex3' <- return $! ((mapIdeal (OP.changeOrder OP.Lex . toOldPoly) ideal3) `using` rdeepseq)
  idealGrlex3 <- return $! (mapIdeal (P.changeOrder P.Grlex) i3 `using` rdeepseq)
  idealGrlex3' <- return $! (mapIdeal (OP.changeOrder OP.Grlex . toOldPoly) i3 `using` rdeepseq)
  ideal4 <- return $! (i4 `using` rdeepseq)
  ideal4' <- return $! ((mapIdeal toOldPoly ideal4) `using` rdeepseq)
  idealGrlex4 <- return $! (mapIdeal (P.changeOrder P.Grlex) i4 `using` rdeepseq)
  idealGrlex4' <- return $! (mapIdeal (OP.changeOrder OP.Grlex . toOldPoly) i4 `using` rdeepseq)
  defaultMain $ [bgroup "case01"
                            [ bgroup "lex"
                              [ bench "old" $ nf (OP.calcGroebnerBasisWith OP.Lex) idealLex1'
                              , bench "acc" $ nf (P.calcGroebnerBasisWith P.Lex) idealLex1
                              ]
                            , bgroup "grlex"
                              [ bench "old" $ nf (OP.calcGroebnerBasisWith OP.Grlex) idealGrlex1'
                              , bench "acc" $ nf (P.calcGroebnerBasisWith P.Grlex) idealGrlex1
                              ]
                            , bgroup "grevlex"
                              [ bench "old" $ nf (OP.calcGroebnerBasisWith OP.Grevlex) ideal1'
                              , bench "acc" $ nf (P.calcGroebnerBasisWith P.Grevlex) ideal1
                              ]
                            ]
                , bgroup "case02"
                            [ bgroup "grlex"
                              [ bench "old" $ nf (OP.calcGroebnerBasisWith OP.Grlex) idealGrlex2'
                              , bench "acc" $ nf (P.calcGroebnerBasisWith P.Grlex) idealGrlex2
                              ]
                            , bgroup "grevlex"
                              [ bench "old" $ nf (OP.calcGroebnerBasisWith OP.Grevlex) ideal2'
                              , bench "acc" $ nf (P.calcGroebnerBasisWith P.Grevlex) ideal2
                              ]
                            ]
               , bgroup "case03"
                            [ bgroup "lex"
                              [ bench "old" $ nf (OP.calcGroebnerBasisWith OP.Lex) idealLex3'
                              , bench "acc" $ nf (P.calcGroebnerBasisWith P.Lex) idealLex3
                              ]
                            , bgroup "grlex"
                              [ bench "old" $ nf (OP.calcGroebnerBasisWith OP.Grlex) idealGrlex3'
                              , bench "acc" $ nf (P.calcGroebnerBasisWith P.Grlex) idealGrlex3
                              ]
                            , bgroup "grevlex"
                              [ bench "old" $ nf (OP.calcGroebnerBasisWith OP.Grevlex) ideal3'
                              , bench "acc" $ nf (P.calcGroebnerBasisWith P.Grevlex) ideal3
                              ]
                            ]
                , bgroup "case04"
                            [ bgroup "grlex"
                              [ bench "old" $ nf (OP.calcGroebnerBasisWith OP.Grlex) idealGrlex4'
                              , bench "acc" $ nf (P.calcGroebnerBasisWith P.Grlex) idealGrlex4
                              ]
                            , bgroup "grevlex"
                              [ bench "old" $ nf (OP.calcGroebnerBasisWith OP.Grevlex) ideal4'
                              , bench "acc" $ nf (P.calcGroebnerBasisWith P.Grevlex) ideal4
                              ]
                            ]
                ]
