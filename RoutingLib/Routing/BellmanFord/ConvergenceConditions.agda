open import Level

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.RoutingAlgebra
import RoutingLib.Routing.Algebra.RoutingAlgebra.FiniteProperties as FiniteRoutingAlgebraProperties
open import RoutingLib.Routing.Algebra.PathAlgebra
open import RoutingLib.Routing.Algebra.CertifiedPathAlgebra
open import RoutingLib.Routing.Algebra.PathAlgebra.Properties
open import RoutingLib.Routing.Algebra.PathAlgebra.Certify

module RoutingLib.Routing.BellmanFord.ConvergenceConditions {a b ℓ} where

----------------------------------------------
-- Conditions for distance-vector protocols --
----------------------------------------------

record IsFiniteStrictlyIncreasingRoutingAlgebra
  (algebra : RawRoutingAlgebra a b ℓ) : Set (suc (a ⊔ b ⊔ ℓ)) where
  field
    isRoutingAlgebra     : IsRoutingAlgebra algebra
    isFinite             : IsFinite algebra
    isStrictlyIncreasing : IsStrictlyIncreasing algebra

  open RawRoutingAlgebra algebra public
  open IsRoutingAlgebra isRoutingAlgebra public
  open FiniteRoutingAlgebraProperties isRoutingAlgebra isFinite public

------------------------------------------
-- Conditions for path-vector protocols --
------------------------------------------

record IsIncreasingPathAlgebra
  (algebra : RawRoutingAlgebra a b ℓ) : Set (suc (a ⊔ b ⊔ ℓ)) where
  field
    isPathAlgebra  : IsPathAlgebra algebra
    isIncreasing   : IsIncreasing algebra

  open RawRoutingAlgebra algebra public
  open IsPathAlgebra isPathAlgebra public

  isCertifiedPathAlgebra : ∀ n → IsCertifiedPathAlgebra algebra n
  isCertifiedPathAlgebra = certifiedPathAlgebra algebra isPathAlgebra

  isStrictlyIncreasing : IsStrictlyIncreasing algebra
  isStrictlyIncreasing = incr⇒strIncr isPathAlgebra isIncreasing
