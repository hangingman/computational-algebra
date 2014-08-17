{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, KindSignatures          #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude, PolyKinds #-}
{-# LANGUAGE StandaloneDeriving, TypeFamilies, TypeOperators     #-}
module Algebra.Ring.Polynomial.Named where
import Algebra.Prelude
import Data.Singletons.Prelude (Symbol)
import Data.Type.Natural
import Numeric.Semiring.Integral (IntegralSemiring)

type family Length (vs :: [k]) where
  Length '[]       = Z
  Length (x ': xs) = S (Length xs)

newtype QPolynomial r ord (vs :: [Symbol]) =
  QPolynomial { runQPolynomial :: OrderedPolynomial r ord (Length vs) }

deriving instance (IsOrder ord, SingI (Length vs), DecidableZero r, Ring r, Eq r)
               => Eq (QPolynomial r ord vs)

deriving instance (Ord r, IsOrder ord, SingI (Length vs), DecidableZero r, Ring r, Eq r)
               => Ord (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Length vs), Ring r)
               => Additive (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Length vs), Ring r)
               => Multiplicative (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Length vs), Ring r)
               => Abelian (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Length vs), Ring r)
               => LeftModule Natural (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Length vs), Ring r)
               => RightModule Natural (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Length vs), Ring r)
               => LeftModule Integer (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Length vs), Ring r)
               => RightModule Integer (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Length vs), Ring r)
               => Monoidal (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Length vs), Ring r)
               => Group (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Length vs), Ring r)
               => Commutative (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Length vs), Ring r)
               => Semiring (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Length vs), Ring r)
               => Unital (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Length vs), Ring r)
               => Rig (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Length vs), Ring r)
               => Ring (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, DecidableUnits r,
                   SingI (Length vs), Ring r)
               => DecidableUnits (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, SingI (Length vs), Ring r)
               => DecidableZero (QPolynomial r ord vs)

deriving instance (IsOrder ord, DecidableZero r, Ring r,
                   SingI (Length vs), IntegralSemiring r)
               => IntegralSemiring  (QPolynomial r ord vs)

deriving instance (IsMonomialOrder ord, IntegralSemiring r,
                   Commutative r, Field r, DecidableZero r,
                   Eq r, DecidableUnits r)
               => Euclidean (QPolynomial r ord '[v])


