-- imports

open import Data.Nat
  using (ℕ; _+_; _≤_; zero; suc; _<_; _≟_; s≤s; z≤n; _∸_; _≤?_; pred)
open import Data.Fin
  using (Fin)
open import Data.Fin.Subset using () renaming (_∈_ to _∈ₛ_; _∉_ to _∉ₛ_)
open import Relation.Binary
  using (Setoid; Rel; Reflexive; Antisymmetric; Transitive; IsEquivalence; _⇒_)
open import Data.Product
  using (∃; _,_; proj₂; proj₁; _×_)
open import Induction.Nat
  using (<-well-founded)
open import Relation.Unary
  using (Pred; _∩_) renaming (_∈_ to _∈ᵤ_; _∉_ to _∉ᵤ_)
open import Induction.WellFounded
  using (Acc; acc)
open import Data.Nat.Properties
  using (≤-trans; ≤-reflexive; +-identityʳ; m≤m+n; <⇒≤;
        <⇒≤pred; ≤+≢⇒<; m+n∸m≡n; ≤-antisym; pred-mono; +-suc; ≤-refl)
open import Relation.Binary.PropositionalEquality
  using (cong₂; subst; _≡_; _≢_; cong; refl) renaming (sym to ≡sym; trans to ≡trans)
open import Data.Fin.Dec
  using (_∈?_)
open import Relation.Nullary
  using (yes; no; ¬_)
open import Relation.Nullary.Negation
  using (contradiction)
open import Data.Fin.Subset
  using () renaming (_∈_ to _∈s_)
open import Function
  using (_∘_)
  
open Setoid
  using (Carrier)
open Data.Nat.Properties.≤-Reasoning

open import RoutingLib.Asynchronous.Schedule using (Schedule; 𝕋)
open import RoutingLib.Asynchronous using (Parallelisation)
import RoutingLib.Asynchronous.Schedule.Times as Times
import RoutingLib.Asynchronous.Schedule.Times.Properties as TimesProperties
open import RoutingLib.Asynchronous.Theorems using (ACO)

module RoutingLib.Asynchronous.Theorems.UresinDubois1 {a}{ℓ}{n}{S : Fin n → Setoid a ℓ}
  (𝕤 : Schedule n)(𝕡 : Parallelisation S) where

  open Schedule 𝕤
  open Parallelisation 𝕡

  open Times 𝕤
  open TimesProperties 𝕤

  φsK≤sk⇒τK≤βsK : ∀ k K i j → φ (suc K) ≤ suc k → τ K j ≤ β (suc k) i j
  φsK≤sk⇒τK≤βsK k K i j p = subst ((τ K j) ≤_)
          (cong (λ x → β x i j) (m+n∸m≡n p))
          (proj₂ (prop1-iii K i j (suc k ∸ (φ (suc K)))))


  module Theorem1 {x₀ : M}(aco : ACO 𝕡)(x₀∈D₀ : x₀ ∈ (ACO.D aco) 0) where
    open ACO aco

    -- Extract the fixed point
    ξ : M
    ξ = proj₁ D-finish

    D-T+K≡ξ : ∀ K → Singleton-t ξ (D (T + K))
    D-T+K≡ξ = proj₂ D-finish

    -- Case lemmas
    
    lemma₁ : (acc₀ : Acc _<_ 0) → ∀ K i → τ K i ≤ zero → async-iter' 𝕤 x₀ acc₀ i ∈ᵤ D K i
    lemma₁ _ K i τ≤0 = subst (x₀ i ∈ᵤ_) (cong (λ k → D k i) 0≡k) (x₀∈D₀ i)
      where
      0≡k : 0 ≡ K
      0≡k = (≤-antisym z≤n (subst (K ≤_) (≤-antisym τ≤0 z≤n) (τ-inc K i)))


    τK≤k⇒xₖ'∈DK : ∀ {k} (accₖ : Acc _<_ k) → ∀ K i → τ K i ≤ k → async-iter' 𝕤 x₀ accₖ i ∈ᵤ D K i
    τK≤k⇒xₖ'∈DK {zero}  acc₀ K i τ≤0 = lemma₁ acc₀ K i τ≤0
    τK≤k⇒xₖ'∈DK {suc k} (acc rs) K i τ≤sk with i ∈? α (suc k)
    τK≤k⇒xₖ'∈DK {suc k} (acc rs) K i τ≤sk | no  i∉α with τ K i ≟ suc k
    ...   | no  τ≢sk = τK≤k⇒xₖ'∈DK (rs k ≤-refl) K i (<⇒≤pred (≤+≢⇒< τ≤sk τ≢sk))
    τK≤k⇒xₖ'∈DK {suc k} (acc rs) zero    i τ≤sk | no i∉α | yes τ≡sk =
      τK≤k⇒xₖ'∈DK {k} (rs k ≤-refl) 0 i z≤n
      

    τK≤k⇒xₖ'∈DK {suc k} (acc rs) (suc K) i τ≤sk | no i∉α | yes τ≡sk = contradiction (subst (i ∈ₛ_) (cong α τ≡sk) (nextActive-active (φ (suc K)) i)) i∉α
    τK≤k⇒xₖ'∈DK {suc k} (acc rs) (suc K) i τ≤sk | yes i∈α = f-monotonic K async∈DK i
               where
               accβ : ∀ j → Acc _<_ (β (suc k) i j)
               accβ j = (rs (β (suc k) i j) (s≤s (causality k i j)))
               
               async∈DK : ∀ j → async-iter' 𝕤 x₀ (accβ j) j ∈ᵤ D K j
               async∈DK j = τK≤k⇒xₖ'∈DK (accβ j) K j (φsK≤sk⇒τK≤βsK k K i j (≤-trans (φ≤τ (suc K) i) τ≤sk))
    τK≤k⇒xₖ'∈DK {suc k} (acc rs) zero    i τ≤sk | yes i∈α with T ≟ 0
    ... | no  T≢0 = D-decreasing 0
          (f (λ j → async-iter' 𝕤 x₀ (rs (β (suc k) i j) (s≤s (causality k i j))) j) )
          (f-monotonic 0 (λ j → τK≤k⇒xₖ'∈DK (rs (β (suc k) i j) (s≤s (causality k i j))) 0 j z≤n)) i
    ... | yes T≡0 = D-subst 0 {x = ξ}
          {y = f[newState]}
          (λ l → proj₂ (D-T+K≡ξ 1) f[newState] (subst (λ v → f[newState] ∈ D v) {x = 1} {y = T + 1}
          (≡sym (cong (_+ 1) T≡0))
          (f-monotonic 0 (λ j → τK≤k⇒xₖ'∈DK (rs (β (suc k) i j) (s≤s (causality k i j))) 0 j z≤n))) l)
          (subst (λ v → ξ ∈ D v) (cong (_+ 0) T≡0) (proj₁ (D-T+K≡ξ 0))) i
          where

          accβ : ∀ j → Acc _<_ (β (suc k) i j)
          accβ j = rs (β (suc k) i j) (s≤s (causality k i j))
          
          newState : M
          newState = (λ j → async-iter' 𝕤 x₀ (accβ j) j)
          
          f[newState] : M
          f[newState] = f newState

 
    τK≤k⇒xₖ∈DK : ∀ k K i → τ K i ≤ k → async-iter 𝕤 x₀ k i ∈ᵤ D K i
    τK≤k⇒xₖ∈DK k K i τK≤k = τK≤k⇒xₖ'∈DK (<-well-founded k) K i τK≤k

    -- Theorem 1

    Tᶜ : 𝕋
    Tᶜ = φ (suc T)

    accTᶜ+K : ∀ K → Acc _<_ (Tᶜ + K)
    accTᶜ+K K = <-well-founded (φ (suc T) + K)

    τ≤Tᶜ+K : ∀ K j → τ (T + 0) j ≤ Tᶜ + K
    τ≤Tᶜ+K K j with T
    ... | zero = z≤n
    ... | suc t = begin 
      τ (suc t + 0) j      ≡⟨ cong₂ τ (+-identityʳ (suc t)) refl ⟩
      τ (suc t) j          ≤⟨ <⇒≤ (nextActiveφ<φs (suc t) j) ⟩
      φ (suc (suc t))      ≤⟨ m≤m+n (φ (suc (suc t))) K ⟩
      φ (suc (suc t)) + K  ∎

    theorem1-proof : ∀ K → async-iter 𝕤 x₀ (Tᶜ + K) ≈ ξ
    theorem1-proof K i = ≈ᵢ-sym (proj₂ (D-T+K≡ξ 0) (async-iter 𝕤 x₀ (Tᶜ + K)) async∈DT i)
      where
      async∈DT : async-iter 𝕤 x₀ (Tᶜ + K) ∈ D (T + 0)
      async∈DT j = τK≤k⇒xₖ∈DK (Tᶜ + K) (T + 0) j (τ≤Tᶜ+K K j)
      
    theorem1 : ∃ λ K → ∀ K₁ → async-iter 𝕤 x₀ (K + K₁) ≈ ξ
    theorem1 = Tᶜ , theorem1-proof
