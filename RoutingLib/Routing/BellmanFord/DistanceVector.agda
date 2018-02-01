open import Data.Nat using (ℕ; zero; suc; _<_)
open import RoutingLib.Data.Nat.Properties using (module ≤-Reasoning)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Routing.BellmanFord.DistanceVector.SufficientConditions
open import RoutingLib.Asynchronous using (Parallelisation; IsAsynchronouslySafe)
open import RoutingLib.Asynchronous.Theorems using (UltrametricConditions; ultra⇒safe)

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

  open RoutingProblem 𝓡𝓟
  open import RoutingLib.Routing.BellmanFord 𝓡𝓟
  open import RoutingLib.Routing.BellmanFord.DistanceVector.Step3_StateMetric 𝓡𝓟 𝓢𝓒
  
  D-strContrIsh : ∀ {X X*} → σ X* ≈ₘ X* → X ≉ₘ X* → D X* (σ X) < D X* X 
  D-strContrIsh {X} {X*} σX*≈X* X≉X* = begin
    D X*     (σ X) ≡⟨ D-cong (≈ₘ-sym σX*≈X*) (≈ₘ-refl {x = σ X}) ⟩
    D (σ X*) (σ X) <⟨ σ-strContr X≉X* ⟩
    D X*     X     ∎
    where open ≤-Reasoning
  
  σ-ultrametricConditions : UltrametricConditions σ∥
  σ-ultrametricConditions = record
    { dᵢ               = dᵢ
    ; dᵢ-isUltrametric = dᵢ-isUltrametric
    ; f-strContrOrbits = σ-strContr
    ; f-cong           = σ-cong
    ; _≟_              = _≟ₘ_
    ; d-bounded        = D-bounded
    ; element          = I
    ; f-strContrIsh    = D-strContrIsh
    } 

  σ-isAsynchronouslySafe : IsAsynchronouslySafe σ∥
  σ-isAsynchronouslySafe = ultra⇒safe σ-ultrametricConditions
