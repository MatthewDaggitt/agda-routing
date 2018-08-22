open import RoutingLib.Data.Matrix using (SquareMatrix)
open import Data.Nat using (zero; suc; s≤s; z≤n; _^_; _+_; _≤_)
open import Function using (case_of_)

open import RoutingLib.Routing.Algebra
open import RoutingLib.Asynchronous using (IsAsynchronouslySafe)
open import RoutingLib.Asynchronous.Properties using (0-IsSafe)
open import RoutingLib.Asynchronous.Convergence.Theorems using (UltrametricConditions; ultra⇒safe)

import RoutingLib.Routing.BellmanFord.AsyncConvergence.DistanceVector.Prelude as DistanceVectorPrelude
import RoutingLib.Routing.BellmanFord.AsyncConvergence.DistanceVector.Step3_StateMetric as DistanceVectorResults
import RoutingLib.Routing.BellmanFord.AsyncConvergence.PathVector.Prelude as PathVectorPrelude
import RoutingLib.Routing.BellmanFord.AsyncConvergence.PathVector.Step5_StateMetric as PathVectorResults


module RoutingLib.Routing.BellmanFord.Theorems where

--------------------------------------------------------------------------------
-- Theorem 1
--
-- σ is always guaranteed to converge asynchronously over any finite, strictly
-- increasing routing algebra.

module Theorem1 {a b ℓ n} (algebra : FiniteStrictlyIncreasingRoutingAlgebra a b ℓ)
         (A : SquareMatrix (FiniteStrictlyIncreasingRoutingAlgebra.Step algebra) n)
         where

  open DistanceVectorPrelude algebra A
  open DistanceVectorResults algebra A

  finiteStrictlyIncr-converges : IsAsynchronouslySafe σ∥
  finiteStrictlyIncr-converges = ultra⇒safe record
    { dᵢ                 = dₜ
    ; dᵢ-isUltrametric   = dₜ-isUltrametric
    ; F-strContrOnOrbits = σ-strContr
    ; F-strContrOnFP     = σ-strContrOnFP
    ; F-cong             = σ-cong
    ; _≟ᵢ_               = _≟ₜ_
    ; d-bounded          = D-bounded
    ; element            = I
    }

--------------------------------------------------------------------------------
-- Theorem 2
--
-- σ is always guaranteed to converge asynchronously over any strictly
-- increasing path algebra.
--
-- A little bit messier than Theorem 1 as we need to deal with the zero case.

module _ {a b ℓ} where

  open PathVectorPrelude using (σ∥)

  incrPaths-converges :  ∀ {n} (algebra : IncreasingPathAlgebra a b ℓ n) →
                         IsAsynchronouslySafe (σ∥ algebra)
  incrPaths-converges {n = zero}  algebra = 0-IsSafe (σ∥ algebra)
  incrPaths-converges {n = suc n} algebra = ultra⇒safe record
    { dᵢ                 = dₜ
    ; dᵢ-isUltrametric   = dₜ-isUltrametric
    ; F-cong             = σ-cong
    ; F-strContrOnOrbits = σ-strContrOrbits
    ; F-strContrOnFP     = σ-strContrOnFP
    ; d-bounded          = D-bounded
    ; element            = I
    ; _≟ᵢ_               = _≟ₜ_
    }
    where
    open PathVectorResults algebra (s≤s z≤n)
    open PathVectorPrelude algebra

--------------------------------------------------------------------------------
-- Theorem 3
--
-- σ is always guaranteed to converge synchronously in n² steps over any
-- increasing path algebra

module Theorem3 {a b ℓ n-1} (algebra : IncreasingPathAlgebra a b ℓ (suc n-1)) where

  open import RoutingLib.Routing.BellmanFord.SyncConvergenceRate.PathVector.Prelude algebra
  open import RoutingLib.Routing.BellmanFord.SyncConvergenceRate.PathVector.Step5_Proof algebra

  σ-convergesIn-n² : ∀ X t → σ^ (n ^ 2 + t) X ≈ₘ σ^ (n ^ 2) X
  σ-convergesIn-n² = n²-convergence
