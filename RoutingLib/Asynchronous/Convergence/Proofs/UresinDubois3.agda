open import Data.Fin using (Fin)
open import Data.Product using (_×_; ∃; proj₁; proj₂; _,_; ∃₂)
open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s; _≟_; _≤?_; _∸_) renaming (_≤_ to _≤ℕ_)
open import Data.Nat.Properties as ℕₚ using (pred-mono; ≤+≢⇒<; ≰⇒≥; +-suc; +-comm; +-identityʳ; m+n∸m≡n; m≤m+n; ≤-step)
-- open import Relation.Binary using (Setoid; Rel; Reflexive; Antisymmetric; Transitive; _⇒_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (_∩_; U) renaming (_∈_ to _∈ᵤ_)

open import RoutingLib.Data.Table using (Table)
open import RoutingLib.Data.Nat.Properties using (m≤n⇒o+m≡n)
open import RoutingLib.Relation.Binary.Indexed.Homogeneous
open import RoutingLib.Relation.Unary.Indexed

open import RoutingLib.Asynchronous using (Parallelisation)
open import RoutingLib.Asynchronous.Convergence.Conditions

module RoutingLib.Asynchronous.Convergence.Proofs.UresinDubois3
  {a ℓ n o p}
  {𝕊ᵢ : Setoid (Fin n) a ℓ}
  (𝓟 : Parallelisation 𝕊ᵢ)
  (syncConditions : SynchronousConditions 𝓟 p o)
  where

  open Parallelisation 𝓟
  open SynchronousConditions syncConditions


  syncIter-mono : ∀ {x} → x ∈ D₀ → ∀ {k t} → k ≤ℕ t → syncIter x t ≤ syncIter x k
  syncIter-mono x∈D₀ {_} {zero}  z≤n = ≤-refl
  syncIter-mono x∈D₀ {k} {suc t} k≤t with k ≟ suc t
  ... | yes refl = ≤-refl
  ... | no  k≢st = ≤-trans (iter-decreasing x∈D₀ t) (syncIter-mono x∈D₀ {k} {t} (pred-mono (≤+≢⇒< k≤t k≢st)))

  syncIter∈D₀ : ∀ {x} → x ∈ D₀ → ∀ K → syncIter x K ∈ D₀
  syncIter∈D₀ x∈D₀ zero    = x∈D₀
  syncIter∈D₀ x∈D₀ (suc K) = D₀-closed (syncIter∈D₀ x∈D₀ K)

  syncIter-fixed : ∀ {x} (x∈D₀ : x ∈ D₀) t → syncIter x (t + proj₁ (iter-converge x∈D₀)) ≈ ξ
  syncIter-fixed x∈D₀ zero    = proj₂ (iter-converge x∈D₀)
  syncIter-fixed x∈D₀ (suc t) = ≈-trans (F-cong (syncIter-fixed x∈D₀ t)) ξ-fixed

  syncIter-fixed′ : ∀ {x} (x∈D₀ : x ∈ D₀) {t} → proj₁ (iter-converge x∈D₀) ≤ℕ t → syncIter x t ≈ ξ
  syncIter-fixed′ x∈D₀ T≤t with m≤n⇒o+m≡n T≤t
  ... | s , refl = syncIter-fixed x∈D₀ s
  
  ξ≤syncIter : ∀ {x} → x ∈ D₀ → ∀ t → ξ ≤ syncIter x t
  ξ≤syncIter {x} x∈D₀ t i with t ≤? proj₁ (iter-converge x∈D₀)
  ... | yes t≤T = ≤ᵢ-respˡ-≈ᵢ (proj₂ (iter-converge x∈D₀) i) (syncIter-mono x∈D₀ t≤T i)
  ... | no  t≰T = ≤ᵢ-reflexive (≈ᵢ-sym (syncIter-fixed′ x∈D₀ (≰⇒≥ t≰T) i))
  
  module _ {x₀} (x₀∈D₀ : x₀ ∈ D₀) where
  
    -- Synchronous iterations
    σ : ℕ → S
    σ = syncIter x₀

    -- Convergence time
    T : ℕ
    T = proj₁ (iter-converge x₀∈D₀)

    ξ∈D₀ : ξ ∈ D₀
    ξ∈D₀ = D₀-cong (syncIter∈D₀ x₀∈D₀ T) (proj₂ (iter-converge x₀∈D₀))
    
    -- Sequence of sets
    D : ℕ → Pred Sᵢ _
    D K {i} = (λ x → (ξ i ≤ᵢ x) × (x ≤ᵢ σ K i)) ∩ D₀ 
    
    x₀∈D[0] : x₀ ∈ D 0
    x₀∈D[0] i = (ξ≤syncIter x₀∈D₀ 0 i , ≤ᵢ-refl) , (x₀∈D₀ i)

    D-decreasing : ∀ K → D (suc K) ⊆ D K
    D-decreasing K x∈DK i with x∈DK i
    ... | ((ξ≤x , x≤iterK), x∈D₀) = (ξ≤x , ≤ᵢ-trans x≤iterK (iter-decreasing x₀∈D₀ K i)) , x∈D₀

    ξ∈D[K] : ∀ K → ξ ∈ D K
    ξ∈D[K] K i = (≤ᵢ-refl , ξ≤syncIter x₀∈D₀ K i) , ξ∈D₀ i

    D-finish′ : ∀ K {x} → x ∈ D (T + K) → ξ ≈ x
    D-finish′ K x∈D[T+K] i rewrite +-comm T K =
      ≤ᵢ-antisym
        (proj₁ (proj₁ (x∈D[T+K] i)))
        (≤ᵢ-trans (proj₂ (proj₁ (x∈D[T+K] i))) (≤ᵢ-reflexive (syncIter-fixed x₀∈D₀ K i)))

    D-finish : ∃₂ λ T ξ → ∀ K → ξ ∈ D (T + K) × (∀ {x} → x ∈ D (T + K) → ξ ≈ x)
    D-finish = T , ξ , λ K → ξ∈D[K] (T + K) , D-finish′ K
    
    F-monotonic  : ∀ K {t} → t ∈ D K → F t ∈ D (suc K)
    F-monotonic K {t} t∈DK i =
      (≤ᵢ-respˡ-≈ᵢ (ξ-fixed i) (F-monotone ξ∈D₀ t∈D₀ ξ≤t i) ,
      F-monotone t∈D₀ (syncIter∈D₀ x₀∈D₀ K) t≤iterK i) ,
      D₀-closed t∈D₀ i
      where
      t∈D₀ : t ∈ D₀
      t∈D₀ j = proj₂ (t∈DK j)

      ξ≤t : ξ ≤ t
      ξ≤t j = proj₁ (proj₁ (t∈DK j))

      t≤iterK : t ≤ σ K
      t≤iterK j = proj₂ (proj₁ (t∈DK j))

    -- Note that this ACO is ONLY for x₀ and for arbitrary x ∈ D₀ it is
    -- not possible to show x ∈ D[0]. This is not made clear in the original
    -- U&D paper.

    aco : ACO 𝓟 _
    aco = record
      { D            = D
      ; D-decreasing = D-decreasing
      ; D-finish     = D-finish
      ; F-monotonic  = F-monotonic  
      }

