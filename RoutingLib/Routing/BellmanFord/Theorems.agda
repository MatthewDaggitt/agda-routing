open import RoutingLib.Data.Matrix using (SquareMatrix)
open import Data.Nat using (zero; suc; s≤s; z≤n; _^_; _+_; _≤_)
open import Function using (case_of_)

open import RoutingLib.Routing.Algebra
open import RoutingLib.Asynchronous using (IsAsynchronouslySafe)
open import RoutingLib.Asynchronous.Properties using (0-IsSafe)
open import RoutingLib.Asynchronous.Convergence.Theorems using (UltrametricConditions; ultra⇒safe)
import RoutingLib.Function.Iteration.Convergence as Convergence

import RoutingLib.Routing.BellmanFord as BellmanFord
open import RoutingLib.Routing.BellmanFord.ConvergenceConditions

import RoutingLib.Routing.BellmanFord.AsyncConvergence.DistanceVector.Prelude as DistanceVectorPrelude
import RoutingLib.Routing.BellmanFord.AsyncConvergence.DistanceVector.Step3_StateMetric as DistanceVectorResults
import RoutingLib.Routing.BellmanFord.AsyncConvergence.PathVector.Prelude as PathVectorPrelude
import RoutingLib.Routing.BellmanFord.AsyncConvergence.PathVector.Step5_StateMetric as PathVectorResults


module RoutingLib.Routing.BellmanFord.Theorems
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) where

open BellmanFord algebra
open module Private {n} {A : AdjacencyMatrix algebra n} = Convergence (ℝ𝕄ₛ A)

--------------------------------------------------------------------------------
-- Theorem 1
--
-- σ is always guaranteed to converge asynchronously over any finite, strictly
-- increasing routing algebra.

module _ (conditions : IsFiniteStrictlyIncreasingRoutingAlgebra algebra) where

  open IsFiniteStrictlyIncreasingRoutingAlgebra conditions
  
  -- open DistanceVectorPrelude isRoutingAlgebra A

  finiteStrictlyIncr-converges : ∀ {n} (A : AdjacencyMatrix algebra n) → IsAsynchronouslySafe (σ∥ A)
  finiteStrictlyIncr-converges A = ultra⇒safe record
    { dᵢ                 = dₜ
    ; dᵢ-isUltrametric   = dₜ-isUltrametric
    ; F-strContrOnOrbits = σ-strContr
    ; F-strContrOnFP     = σ-strContrOnFP
    ; F-cong             = σ-cong A
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
  
  incrPaths-converges :  ∀ {n} (A : AdjacencyMatrix algebra n) → IsAsynchronouslySafe (σ∥ A)
  incrPaths-converges {n = zero}  A = 0-IsSafe (σ∥ A)
  incrPaths-converges {n = suc n} A = ultra⇒safe record
    { dᵢ                 = dₜ
    ; dᵢ-isUltrametric   = dₜ-isUltrametric
    ; F-cong             = σ-cong A
    ; F-strContrOnOrbits = σ-strContrOrbits
    ; F-strContrOnFP     = σ-strContrOnFP
    ; d-bounded          = D-bounded
    ; element            = I A
    ; _≟ᵢ_               = _≟ₜ_ A
    }
    where
    open PathVectorResults (isCertifiedPathAlgebra (suc n)) isStrictlyIncreasing A (s≤s z≤n)
    
--------------------------------------------------------------------------------
-- Theorem 3
--
-- σ is always guaranteed to converge synchronously in n² steps over any
-- increasing path algebra

module _ (conditions : IsIncreasingPathAlgebra algebra) where

  open IsIncreasingPathAlgebra conditions
  
  σ-convergesIn-n² : ∀ {n} (A : AdjacencyMatrix algebra n) → (σ A) ConvergesIn (n ^ 2)
  σ-convergesIn-n² = {!!}
{-
  {zero}    A X t ()
  σ-convergesIn-n² {suc n-1} A = n²-convergence
    where
    open import RoutingLib.Routing.BellmanFord.SyncConvergenceRate.PathVector.Prelude (isCertifiedPathAlgebra (suc n-1)) A
    open import RoutingLib.Routing.BellmanFord.SyncConvergenceRate.PathVector.Step5_Proof (isCertifiedPathAlgebra (suc n-1)) isIncreasing A
-}
