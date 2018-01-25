open import Data.Nat using (ℕ; zero; suc)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Routing.BellmanFord.DistanceVector.SufficientConditions
open import RoutingLib.Asynchronous using (IsAsynchronouslySafe)
open import RoutingLib.Asynchronous.Theorems.Core using (UltrametricConditions)
open import RoutingLib.Asynchronous.Theorems using (ultra⇒safe)

module RoutingLib.Routing.BellmanFord.DistanceVector
  {a b ℓ n-1}
  (𝓡𝓐 : RoutingAlgebra a b ℓ)
  (𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1))
  (𝓢𝓒 : SufficientConditions 𝓡𝓐)
  where

  ------------------------------------------------------------------------
  -- Theorem
  --
  -- Distributed Bellman Ford used as a distance vector algorithm converges
  -- from any state when it is possible to enumerate all values of Route

  open RoutingProblem 𝓡𝓟 using (_≟ₘ_)
  open import RoutingLib.Routing.BellmanFord 𝓡𝓟
  open import RoutingLib.Routing.BellmanFord.DistanceVector.Step3_StateMetric 𝓡𝓟 𝓢𝓒
    using (dᵢ; dᵢ-isUltrametric; D-bounded; σ-strictlyContracting)

  σ-ultrametricConditions : UltrametricConditions σ∥
  σ-ultrametricConditions = record
    { dᵢ               = dᵢ
    ; dᵢ-isUltrametric = dᵢ-isUltrametric
    ; f-strContrOver-d = σ-strictlyContracting
    ; f-cong           = σ-cong
    ; _≟_              = _≟ₘ_
    ; d-bounded        = D-bounded
    ; element          = I
    } 

  σ-isAsynchronouslySafe : IsAsynchronouslySafe σ∥
  σ-isAsynchronouslySafe = ultra⇒safe σ-ultrametricConditions
