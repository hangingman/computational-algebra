{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses, StandaloneDeriving    #-}
module Algebra.Scalar (Scalar(..), (.*.)) where
import Algebra.Ring.Noetherian
import Numeric.Algebra

newtype Scalar r = Scalar { runScalar :: r }
    deriving (Read, Show, Eq, Ord, Additive, Num, Integral, Real, Enum
             ,Multiplicative, Unital)

(.*.) :: (RightModule (Scalar r) m, LeftModule (Scalar r) m)
      => r -> m -> m
r .*. f = Scalar r .* f

infixl 7 .*.

deriving instance Monoidal r => Monoidal (Scalar r)
deriving instance Group r => Group (Scalar r)
deriving instance Semiring r => Semiring (Scalar r)
deriving instance Ring r => Ring (Scalar r)
deriving instance Abelian r => Abelian (Scalar r)
deriving instance Rig r => Rig (Scalar r)
deriving instance Commutative r => Commutative (Scalar r)
deriving instance Division r => Division (Scalar r)
deriving instance NoetherianRing r => NoetherianRing (Scalar r)

instance LeftModule Integer r => LeftModule Integer (Scalar r) where
  n .* Scalar r = Scalar $ n .* r
instance RightModule Integer r => RightModule Integer (Scalar r) where
  Scalar r *. n = Scalar $ r *. n
instance LeftModule Natural r => LeftModule Natural (Scalar r) where
  n .* Scalar r = Scalar $ n .* r
instance RightModule Natural r => RightModule Natural (Scalar r) where
  Scalar r *. n = Scalar $ r *. n