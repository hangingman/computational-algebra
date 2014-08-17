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
import Data.Type.Ordinal (Ordinal)
import Data.Vector.Sized (Vector)
import Data.Singletons.Prelude
import Data.Vector.Sized ((%!!))
import GHC.TypeLits hiding (Nat)
import qualified GHC.TypeLits as TL
import Data.Singletons.TH (genDefunSymbols)
import Data.Singletons.Decide
import Data.Singletons.TypeLits (withKnownNat)
import Unsafe.Coerce (unsafeCoerce)
import Data.Singletons.Prelude.Maybe
import Data.Proxy (Proxy)
import GHC.Exts (Constraint)
import qualified Data.Vector.Sized as V
import Control.Lens ((&))
import qualified Prelude as P

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
  FindIndex (x ': xs) x = Just 0
  FindIndex (y ': xs) x = RecFindInd (FindIndex xs x)

type family RecFindInd (m :: Maybe TL.Nat) :: Maybe TL.Nat
type instance RecFindInd Nothing  = Nothing
type instance RecFindInd (Just n) = Just (n + 1)

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
    Proved Refl -> SJust (sing :: Sing 0)
    Disproved _ -> unsafeCoerce $  sRecFindInd (sFindIndex xs y)

sRecFindInd :: SMaybe n -> SMaybe (RecFindInd n)
sRecFindInd SNothing  = SNothing
sRecFindInd (SJust (n :: Sing n)) = SJust (unsafeCoerce n :: Sing (n + 1))

type family BelongsTo xs x :: Constraint where
   BelongsTo (x ': xs) x = ()
   BelongsTo (y ': ys) x = BelongsTo ys x

type family AllC (p :: k -> Constraint) (xs :: [k]) :: Constraint where
  AllC p '[] = ()
  AllC p (x ': xs) = (p x, AllC p xs)

naturalInjection :: forall pxy vs vs' r ord.
                    (SingI (Len vs'), SingI (Len vs), SingI (Permute vs vs'),
                     AllC (BelongsTo vs') vs, IsOrder ord, DecidableZero r,
                     Ring r)
                 => pxy vs' -> QPolynomial r ord vs -> QPolynomial r ord vs'
naturalInjection _ (QPolynomial f) =
  let ids = fromSing (sing :: SList (Permute vs vs'))
      build m = V.unsafeFromList' $ map (maybe 0 ((m %!!) . P.fromInteger)) ids
  in QPolynomial $ transformMonomial build f
