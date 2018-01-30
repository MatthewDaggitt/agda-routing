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
open import Relation.Unary using () renaming (_∈_ to _∈ᵤ_)
open import Data.Fin.Subset
  using () renaming (_∈_ to _∈ₛ_)
open import Function
  using (_∘_)
  
open Setoid
  using (Carrier)
open Data.Nat.Properties.≤-Reasoning

open import RoutingLib.Asynchronous.Schedule using (Schedule; 𝕋)
open import RoutingLib.Asynchronous using (Parallelisation; IsAsynchronouslySafe)
import RoutingLib.Asynchronous.Schedule.Times as Times
import RoutingLib.Asynchronous.Schedule.Times.Properties as TimesProperties
open import RoutingLib.Asynchronous.Theorems.Core using (TotalACO; ACO)

module RoutingLib.Asynchronous.Theorems.UresinDubois1
  {a ℓ n} {S : Fin n → Setoid a ℓ} (𝕡 : Parallelisation S) where

  open Parallelisation 𝕡

  module _ {p} {x₀ : M} (aco : ACO 𝕡 p) (𝕤 : Schedule n) (x₀∈D₀ : x₀ ∈ (ACO.D aco 0)) where
    open ACO aco

    open Schedule 𝕤
    open Times 𝕤
    open TimesProperties 𝕤

{-
    φsK≤sk⇒τK≤βsK : ∀ k K i j → φ (suc K) ≤ suc k → τ K j ≤ β (suc k) i j
    φsK≤sk⇒τK≤βsK k K i j p = subst (τ K j ≤_)
          (cong (λ x → β x i j) (m+n∸m≡n p))
          (proj₂ (prop1-iii K i j (suc k ∸ (φ (suc K)))))
-}

    φsK≤t⇒τK≤βt : ∀ {t K i j} → ϕ (suc K) ≤ t → τ K j ≤ β t i j
    φsK≤t⇒τK≤βt {t} {K} {i} {j} ϕsK≤t = subst (τ K j ≤_)
          (cong (λ x → β x i j) (m+n∸m≡n ϕsK≤t))
          (proj₂ (ϕ≤τ≤βϕs+t K i j (t ∸ (ϕ (suc K)))))
    -- Extract the fixed point

    T : 𝕋
    T = proj₁ D-finish

    ξ : M
    ξ = proj₁ (proj₂ D-finish)

    D-T+K≡ξ : ∀ K → isSingleton ξ (D (T + K))
    D-T+K≡ξ = proj₂ (proj₂ D-finish)


    async'ₜ∈D₀ : ∀ {t} (accₜ : Acc _<_ t) → async-iter' 𝕤 x₀ accₜ ∈ D 0
    async'ₜ∈D₀ {zero}  _ = x₀∈D₀
    async'ₜ∈D₀ {suc t} (acc rs) i with i ∈? α (suc t)
    ... | yes i∈α = D-decreasing 0 (f-monotonic 0 (λ j →
          async'ₜ∈D₀ (rs (β (suc t) i j) (s≤s (causality t i j))) j)) i
    ... | no  i∉α = async'ₜ∈D₀ (rs t (s≤s ≤-refl)) i

    -- Case lemmas
    
    lemma₁ : (acc₀ : Acc _<_ 0) → ∀ K i → τ K i ≤ zero → async-iter' 𝕤 x₀ acc₀ i ∈ᵤ D K i
    lemma₁ _ K i τ≤0 = subst (x₀ i ∈ᵤ_) (cong (λ k → D k i) 0≡k) (x₀∈D₀ i)
      where
      0≡k : 0 ≡ K
      0≡k = (≤-antisym z≤n (subst (K ≤_) (≤-antisym τ≤0 z≤n) (τ-inc K i)))


    τK≤t⇒xₜ'∈DK : ∀ {t} (accₜ : Acc _<_ t) → ∀ K i → τ K i ≤ t → async-iter' 𝕤 x₀ accₜ i ∈ᵤ D K i
    τK≤t⇒xₜ'∈DK {zero}  acc₀ K i τ≤0 = lemma₁ acc₀ K i τ≤0
    τK≤t⇒xₜ'∈DK {suc t} (acc rs) K i τ≤st with i ∈? α (suc t)
    ...  | no  i∉α with τ K i ≟ suc t
    ...    | no  τ≢st = τK≤t⇒xₜ'∈DK (rs t ≤-refl) K i (<⇒≤pred (≤+≢⇒< τ≤st τ≢st))
    τK≤t⇒xₜ'∈DK {suc t} (acc rs) zero i τ≤st | no i∉α | yes τ≡st =
      async'ₜ∈D₀ (rs t (s≤s (≤-refl))) i
    τK≤t⇒xₜ'∈DK {suc t} (acc rs) (suc K) i τ≤st | no i∉α | yes τ≡st = contradiction (subst (i ∈ₛ_) (cong α τ≡st) (nextActive-active (ϕ (suc K)) i)) i∉α
    τK≤t⇒xₜ'∈DK {suc t} (acc rs) (suc K) i τ≤st | yes i∈α = f-monotonic K async∈DK i
               where
               accβ : ∀ j → Acc _<_ (β (suc t) i j)
               accβ j = (rs (β (suc t) i j) (s≤s (causality t i j)))
              
               async∈DK : ∀ j → async-iter' 𝕤 x₀ (accβ j) j ∈ᵤ D K j
               async∈DK j = τK≤t⇒xₜ'∈DK (accβ j) K j (φsK≤t⇒τK≤βt (≤-trans (ϕ≤τ (suc K) i) τ≤st))
    τK≤t⇒xₜ'∈DK {suc t} (acc rs) zero    i τ≤st | yes i∈α with T ≟ 0
    ... | no  T≢0 = D-decreasing 0 (f-monotonic 0
        (λ j → async'ₜ∈D₀ (rs (β (suc t) i j) (s≤s (causality t i j))) j)) i
    ... | yes T≡0 = D-subst 0 {x = ξ}
          {y = f[newState]}
          (λ l → proj₂ (D-T+K≡ξ 1) f[newState] (subst (λ v → f[newState] ∈ D v) {x = 1} {y = T + 1}
          (≡sym (cong (_+ 1) T≡0))
          (f-monotonic 0 λ j → async'ₜ∈D₀ (rs (β (suc t) i j) (s≤s (causality t i j))) j)) l)
          (subst (λ v → ξ ∈ D v) (cong (_+ 0) T≡0) (proj₁ (D-T+K≡ξ 0))) i
          where
          accβ : ∀ j → Acc _<_ (β (suc t) i j)
          accβ j = rs (β (suc t) i j) (s≤s (causality t i j))
          
          newState : M
          newState = (λ j → async-iter' 𝕤 x₀ (accβ j) j)
          
          f[newState] : M
          f[newState] = f newState

 
    τK≤t⇒xₜ∈DK : ∀ t K i → τ K i ≤ t → async-iter 𝕤 x₀ t i ∈ᵤ D K i
    τK≤t⇒xₜ∈DK t K i τK≤k = τK≤t⇒xₜ'∈DK (<-well-founded t) K i τK≤k

    -- Theorem 1

    Tᶜ : 𝕋
    Tᶜ = ϕ (suc T)

    accTᶜ+K : ∀ K → Acc _<_ (Tᶜ + K)
    accTᶜ+K K = <-well-founded (Tᶜ + K)

    τ≤Tᶜ+K : ∀ K j → τ (T + 0) j ≤ Tᶜ + K
    τ≤Tᶜ+K K j = begin 
      τ (T + 0) j ≡⟨ cong₂ τ (+-identityʳ T) refl ⟩
      τ T j       ≤⟨ <⇒≤ (nextActiveϕ<ϕs T j) ⟩
      Tᶜ          ≤⟨ m≤m+n Tᶜ K ⟩
      Tᶜ + K      ∎

    async∈DT : ∀ K → async-iter 𝕤 x₀ (Tᶜ + K) ∈ D (T + 0)
    async∈DT K j = τK≤t⇒xₜ∈DK (Tᶜ + K) (T + 0) j (τ≤Tᶜ+K K j)

    async-converge : ∃ λ T → ∀ K → async-iter 𝕤 x₀ (T + K) ≈ ξ
    async-converge = Tᶜ ,
      (λ K → ≈-sym (proj₂ (D-T+K≡ξ 0) (async-iter 𝕤 x₀ (Tᶜ + K)) (async∈DT K)))


  module _ {p} (totalACO : TotalACO 𝕡 p) where

    open TotalACO totalACO
    
    isAsynchronouslySafe : IsAsynchronouslySafe 𝕡
    isAsynchronouslySafe = record
      { m*         = proj₁ (proj₂ D-finish)
      ; m*-reached = λ 𝕤 X → async-converge aco 𝕤 (total X)
      }
