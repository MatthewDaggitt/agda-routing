open import Level
open import Data.Nat using (ℕ)

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.RoutingAlgebra
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
    isStrictlyIncreasing : IsStrictlyIncreasing algebra
    isFinite             : IsFinite algebra

  open RawRoutingAlgebra algebra public
  open IsRoutingAlgebra isRoutingAlgebra public
  
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
