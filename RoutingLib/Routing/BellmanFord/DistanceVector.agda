open import RoutingLib.Routing.Definitions
open import RoutingLib.Routing.BellmanFord.DistanceVector.SufficientConditions
open import RoutingLib.Asynchronous using (IsAsynchronouslySafe)
open import RoutingLib.Asynchronous.Theorems using (UltrametricConditions; ultra⇒safe)

import RoutingLib.Routing.BellmanFord.DistanceVector.Step3_StateMetric as Step3
import RoutingLib.Routing.BellmanFord.DistanceVector.Prelude as Prelude
module RoutingLib.Routing.BellmanFord.DistanceVector
  {a b ℓ n}
  {𝓡𝓐 : RoutingAlgebra a b ℓ}
  (𝓡𝓟 : RoutingProblem 𝓡𝓐 n)
  (𝓢𝓒 : SufficientConditions 𝓡𝓐)
  where

  ------------------------------------------------------------------------
  -- Theorem
  --
  -- Distributed Bellman Ford used as a distance vector algorithm converges
  -- from any state when it is possible to enumerate all values of Route

  open Prelude 𝓡𝓟 𝓢𝓒
  open Step3 𝓡𝓟 𝓢𝓒
  
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
