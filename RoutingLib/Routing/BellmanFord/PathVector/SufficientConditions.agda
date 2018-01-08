open import Level using (_⊔_)
open import Data.Product using (Σ; ∃; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec)
import Algebra.FunctionProperties as FunctionProperties

open import RoutingLib.Routing.Definitions
open import RoutingLib.Data.Graph.SimplePath
  using (SimplePath; []; [_]; _∺_∣_; _∷_∣_; _∈_; source)
  renaming (_≈_ to _≈ₚ_)

module RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions  where

  ----------------
  -- With paths --
  ----------------
  -- Sufficient conditions for the convergence of the synchronous
  -- Distributed Bellman Ford from any state when the algebra
  -- is lexed with paths

  record PathSufficientConditions
    {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
    {n} (𝓡𝓟 : RoutingProblem 𝓡𝓐 n) : Set (a ⊔ b ⊔ ℓ) where

    open RoutingProblem 𝓡𝓟
    open FunctionProperties _≈_
    
    field
      -- Operator properties
      ⊕-assoc     : Associative _⊕_
      ⊕-sel       : Selective   _⊕_
      ⊕-comm      : Commutative _⊕_
      ⊕-almost-strictly-absorbs-▷ : ∀ s {r} → r ≉ 0# → ((s ▷ r) ⊕ r ≈ r) × (r ≉ s ▷ r)

      -- Element properties
      1#-anᵣ-⊕ : RightZero 1# _⊕_
      0#-an-▷  : ∀ e → e ▷ 0# ≈ 0#
      0#-idᵣ-⊕ : RightIdentity 0# _⊕_

      -- Path
      path              : ∀ {r : Route} → r ≉ 0# → SimplePath n
      path-cong         : ∀ {r s} → r ≈ s → (r≉0 : r ≉ 0#) (s≉0 : s ≉ 0#) → path r≉0 ≈ₚ path s≉0
      path-looping      : ∀ {i} j {r} (r≉0 : r ≉ 0#) → i ∈ path r≉0 → A i j ▷ r ≈ 0#
      path-extension₁   : ∀ {i j r} (r≉0 : r ≉ 0#) (Aᵢⱼ▷r≉0 : A i j ▷ r ≉ 0#) → path r≉0 ≈ₚ [] → ∃ λ i≢j → path Aᵢⱼ▷r≉0 ≈ₚ [ i ∺ j ∣ i≢j ]
      path-extension₂   : ∀ {i j r} (r≉0 : r ≉ 0#) (Aᵢⱼ▷r≉0 : A i j ▷ r ≉ 0#) → ∀ {p} → path r≉0 ≈ₚ [ p ] →
                         j ≡ source p × ∃ λ i∉p → path Aᵢⱼ▷r≉0 ≈ₚ [ i ∷ p ∣ i∉p ]
      path[1]≈[]        : path 1≉0 ≈ₚ []

      path-inconsistent : ∀ (p : SimplePath n) →
                            Dec (∃ λ r → Σ (r ≉ 0#) (λ r≉0 →
                              ((path r≉0) ≈ₚ p) × (weight (path r≉0) ≉ r)))
      path-consistency : ∀ e {r} (r≉0 : r ≉ 0#) (e▷r≉0 : e ▷ r ≉ 0#) →
                       weight (path r≉0) ≈ r → weight (path e▷r≉0) ≈ e ▷ r
  
      
