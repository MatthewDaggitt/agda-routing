open import Data.Nat using (ℕ; zero; suc; _<_)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Algebra.FunctionProperties
open import RoutingLib.Data.Graph
open import RoutingLib.Asynchronous
open import RoutingLib.Asynchronous.Theorems using (UltrametricConditions; ultra⇒safe)
open import Relation.Binary using (IsDecEquivalence; DecSetoid)
open import RoutingLib.Data.Nat.Properties using (module ≤-Reasoning)
open import Function using (_∘_)

open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions using (PathSufficientConditions)
import RoutingLib.Routing.BellmanFord.PathVector.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.PathVector.Step6_StateMetric as Step6
import RoutingLib.Function.Distance.FixedPoint as FixedPoints

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
  open Step6 𝓟𝓢𝓒

  open Parallelisation σ∥ using () renaming (≈-isEquivalence to ≈-isEquivalence')
  
  ≈-isDecEquivalence' : IsDecEquivalence _≈ₘ_
  ≈-isDecEquivalence' = record
      { isEquivalence = ≈-isEquivalence'
      ; _≟_           = _≟ₘ_
      }

  M-decSetoid : DecSetoid _ _
  M-decSetoid = record
      { Carrier          = RMatrix
      ; _≈_              = _≈ₘ_
      ; isDecEquivalence = ≈-isDecEquivalence'
      }
      
  X* : RMatrix
  X* = FixedPoints.x* M-decSetoid D D-strContrOrbits I

  σX*≈X* : σ X* ≈ₘ X*
  σX*≈X* = FixedPoints.x*-fixed M-decSetoid D D-strContrOrbits I
  
  D-strContrIsh : ∀ {X} → X ≉ₘ X* → D X* (σ X) < D X* X 
  D-strContrIsh {X} X≉X* = begin
    D X*     (σ X) ≡⟨ D-cong (≈ₘ-sym σX*≈X*) (≈ₘ-refl {x = σ X}) ⟩
    D (σ X*) (σ X) <⟨ D-strContrᶜ (fixedᶜ σX*≈X*) (X≉X* ∘ ≈ₘ-sym) ⟩
    D X*     X     ∎
    where open ≤-Reasoning

  ultrametricConditions : UltrametricConditions σ∥
  ultrametricConditions = record
    { dᵢ               = dₜ
    ; dᵢ-isUltrametric = dₜ-isUltrametric
    ; f-strContrOrbits = D-strContrOrbits
    ; d-bounded        = D-bounded
    ; element          = I
    ; f-cong           = σ-cong
    ; _≟_              = _≟ₘ_
    ; f-strContrIsh    = D-strContrIsh
    }
  
  σ-isAsynchronouslySafe : IsAsynchronouslySafe σ∥
  σ-isAsynchronouslySafe = ultra⇒safe ultrametricConditions
