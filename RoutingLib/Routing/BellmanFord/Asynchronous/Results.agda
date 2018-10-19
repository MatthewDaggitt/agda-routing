open import RoutingLib.Data.Matrix using (SquareMatrix)
open import Data.Nat using (zero; suc; s≤s; z≤n; _^_; _+_; _≤_)
open import Function using (case_of_)

open import RoutingLib.Routing.Algebra
open import RoutingLib.Iteration.Asynchronous.Dynamic using (IsSafe)
open import RoutingLib.Iteration.Asynchronous.Dynamic.Properties using (0-IsSafe)
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Theorems using (UltrametricConditions; ultra⇒safety)
open import RoutingLib.Iteration.Asynchronous.Schedule using (Epoch)

import RoutingLib.Routing.BellmanFord.Asynchronous as BellmanFord
open import RoutingLib.Routing.BellmanFord.ConvergenceConditions

import RoutingLib.Routing.BellmanFord.Synchronous.Convergence.DistanceVector.Prelude as DistanceVectorPrelude
import RoutingLib.Routing.BellmanFord.Synchronous.Convergence.DistanceVector.Step3_StateMetric as DistanceVectorResults
import RoutingLib.Routing.BellmanFord.Synchronous.Convergence.PathVector.Prelude as PathVectorPrelude
import RoutingLib.Routing.BellmanFord.Synchronous.Convergence.PathVector.Step5_StateMetric as PathVectorResults


module RoutingLib.Routing.BellmanFord.Asynchronous.Results
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) where

open BellmanFord algebra
-- open module Private {n} {A : AdjacencyMatrix algebra n} = Convergence (ℝ𝕄ₛ A)

--------------------------------------------------------------------------------
-- Theorem 1
--
-- σ is always guaranteed to converge asynchronously over any finite, strictly
-- increasing routing algebra.

module _ (conditions : IsFiniteStrictlyIncreasingRoutingAlgebra algebra) where

  open IsFiniteStrictlyIncreasingRoutingAlgebra conditions
  
  -- open DistanceVectorPrelude isRoutingAlgebra A

  finiteStrictlyIncr-converges : ∀ {n} (A : Epoch → AdjacencyMatrix n) → IsSafe (σ∥ A)
  finiteStrictlyIncr-converges A = ultra⇒safety record
    { dᵢ                 = dₜ
    ; dᵢ-isUltrametric   = dₜ-isUltrametric
    ; F-strContrOnOrbits = σ-strContr
    ; F-strContrOnFP     = σ-strContrOnFP
    ; F-cong             = F-cong A
    ; _≟ᵢ_               = _≟ₜ_ A
    ; d-bounded          = D-bounded
    ; element            = I A
    }
    where
    open DistanceVectorResults isRoutingAlgebra isFinite isStrictlyIncreasing A

--------------------------------------------------------------------------------
-- Theorem 2
--
-- σ is always guaranteed to converge asynchronously over any strictly
-- increasing path algebra.
--
-- A little bit messier than Theorem 1 as we need to deal with the zero case.

module _ (conditions : IsIncreasingPathAlgebra algebra) where

  open IsIncreasingPathAlgebra conditions
  
  incrPaths-converges :  ∀ {n} (A : Epoch → AdjacencyMatrix algebra n) → IsSafe (σ∥ A)
  incrPaths-converges {n = zero}  A = 0-IsSafe (σ∥ A)
  incrPaths-converges {n = suc n} A = ultra⇒safety record
    { dᵢ                 = dₜ
    ; dᵢ-isUltrametric   = dₜ-isUltrametric
    ; F-cong             = F-cong A
    ; F-strContrOnOrbits = σ-strContrOrbits
    ; F-strContrOnFP     = σ-strContrOnFP
    ; d-bounded          = D-bounded
    ; element            = I A
    ; _≟ᵢ_               = _≟ₜ_ A
    }
    where
    open PathVectorResults (isCertifiedPathAlgebra (suc n)) isStrictlyIncreasing A (s≤s z≤n)
