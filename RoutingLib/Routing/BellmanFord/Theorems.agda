open import RoutingLib.Data.Matrix using (SquareMatrix)
open import Data.Nat using (suc; _^_; _+_)

open import RoutingLib.Routing.Algebra
open import RoutingLib.Asynchronous using (IsAsynchronouslySafe)
open import RoutingLib.Asynchronous.Theorems using (UltrametricConditions; ultra⇒safe)

module RoutingLib.Routing.BellmanFord.Theorems where

--------------------------------------------------------------------------------
-- Theorem 1
--
-- σ is always guaranteed to converge asynchronously over any finite, strictly
-- increasing routing algebra.

module Theorem1 {a b ℓ n} (algebra : FiniteStrictlyIncreasingRoutingAlgebra a b ℓ)
         (A : SquareMatrix (FiniteStrictlyIncreasingRoutingAlgebra.Step algebra) n)
         where
  
  open import RoutingLib.Routing.BellmanFord.AsyncConvergence.DistanceVector.Prelude algebra A
  open import RoutingLib.Routing.BellmanFord.AsyncConvergence.DistanceVector.Step3_StateMetric algebra A

  σ-ultrametricConditions : UltrametricConditions σ∥
  σ-ultrametricConditions = record
    { dᵢ                = dₜ
    ; dᵢ-isUltrametric  = dₜ-isUltrametric
    ; f-strContrOrbits = σ-strContr
    ; f-strContrOnFP   = σ-strContrOnFP
    ; f-cong           = σ-cong
    ; _≟_              = _≟ₘ_
    ; d-bounded        = D-bounded
    ; element          = I
    } 

  σ-isAsynchronouslySafe : IsAsynchronouslySafe σ∥
  σ-isAsynchronouslySafe = ultra⇒safe σ-ultrametricConditions


--------------------------------------------------------------------------------
-- Theorem 2
--
-- σ is always guaranteed to converge asynchronously over any strictly
-- increasing path algebra.

module Theorem2 {a b ℓ n} (algebra : StrictlyIncreasingPathAlgebra a b ℓ n) where
         
  open import RoutingLib.Routing.BellmanFord.AsyncConvergence.PathVector.Prelude algebra
  open import RoutingLib.Routing.BellmanFord.AsyncConvergence.PathVector.Step5_StateMetric algebra

  ultrametricConditions : UltrametricConditions σ∥
  ultrametricConditions = record
    { dᵢ                = dₜ
    ; dᵢ-isUltrametric  = dₜ-isUltrametric
    ; f-cong           = σ-cong
    ; f-strContrOrbits = σ-strContrOrbits
    ; f-strContrOnFP   = σ-strContrOnFP
    ; d-bounded        = D-bounded
    ; element          = I
    ; _≟_              = _≟ₘ_
    }

  σ-isAsynchronouslySafe : IsAsynchronouslySafe σ∥
  σ-isAsynchronouslySafe = ultra⇒safe ultrametricConditions

--------------------------------------------------------------------------------
-- Theorem 3
--
-- σ is always guaranteed to converge synchronously in n² steps over any
-- increasing (?) path algebra

module Theorem3 {a b ℓ n-1} (algebra : IncreasingPathAlgebra a b ℓ (suc n-1)) where
  
  open import RoutingLib.Routing.BellmanFord.SyncConvergenceRate.PathVector.Prelude algebra
  open import RoutingLib.Routing.BellmanFord.SyncConvergenceRate.PathVector.Step5_Proof algebra

  σ-convergesIn-n² : ∀ X t → σ^ (n ^ 2 + t) X ≈ₘ σ^ (n ^ 2) X
  σ-convergesIn-n² = n²-convergence
