open import Data.Nat using (ℕ; zero; suc)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Algebra.FunctionProperties
open import RoutingLib.Data.Graph
open import RoutingLib.Asynchronous
open import RoutingLib.Asynchronous.Theorems using (UltrametricConditions; ultra⇒safe)

open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions using (PathSufficientConditions)
import RoutingLib.Routing.BellmanFord.PathVector.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.PathVector.Step6_StateMetric as Step6
import RoutingLib.Routing.BellmanFord.PathVector.Step5_TableMetric as Step5

module RoutingLib.Routing.BellmanFord.PathVector
  {a b n-1 ℓ}
  (𝓡𝓐 : RoutingAlgebra a b ℓ)
  (𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1))
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  (G : Graph (RoutingAlgebra.Step 𝓡𝓐) (suc n-1))
  where


  ------------------------------------------------------------------------
  -- Theorem 3
  --
  -- Distributed Bellman Ford converges from any state over any
  -- structure (A,⊕,▷,0,1) when paths are added to it 
  -- as long as ⊕ is associative, commutative, selective and ⊕ absorbs ▷.
  
  open Prelude 𝓟𝓢𝓒
  open Step5 𝓟𝓢𝓒
  open Step6 𝓟𝓢𝓒
  
  ultrametricConditions : UltrametricConditions σ∥
  ultrametricConditions = record
    { dᵢ               = dₜ
    ; element          = I
    ; dᵢ-isUltrametric = dₜ-isUltrametric
    ; f-strContrOver-d = dₘ-strContracting
    ; f-cong           = σ-cong
    ; _≟_              = _≟ₘ_
    ; d-bounded        = dₘ-bounded
    }
  
  σ-isAsynchronouslySafe : IsAsynchronouslySafe σ∥
  σ-isAsynchronouslySafe = ultra⇒safe ultrametricConditions
