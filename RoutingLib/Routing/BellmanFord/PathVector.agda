open import Data.Nat using (suc)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Asynchronous
  using (IsAsynchronouslySafe)
open import RoutingLib.Asynchronous.Theorems
  using (UltrametricConditions; ultra⇒safe)

open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions
import RoutingLib.Routing.BellmanFord.PathVector.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.PathVector.Step6_StateMetric as Step6

module RoutingLib.Routing.BellmanFord.PathVector
  {a b n-1 ℓ}
  {𝓡𝓐 : RoutingAlgebra a b ℓ}
  (𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1))
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  where

  ------------------------------------------------------------------------
  -- Theorem 3
  --
  -- Distributed Bellman Ford converges from any state over any
  -- structure (S,⊕,▷,0,1) when paths are added to it 
  -- as long as ⊕ is associative, commutative, selective and ⊕ absorbs ▷.
  
  open Prelude 𝓟𝓢𝓒
  open Step6 𝓟𝓢𝓒

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
