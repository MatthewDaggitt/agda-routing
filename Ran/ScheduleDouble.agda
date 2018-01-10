-- imports
open import Schedule
  using (𝕋)
open import Data.Nat
  using (ℕ; zero; suc; _≤_; _+_; _<_)
open import Data.Fin
  using (Fin; toℕ)
open import Data.Fin.Subset
  using (Subset; _∈_; ⊤)
open import Data.Product
  using (∃; _,_; proj₁)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; subst; cong; trans)
open import Data.Nat.Properties
  using (+-suc; +-identityʳ; ≤-reflexive)
open import Induction.WellFounded
  using (Acc; acc)
open import Induction.Nat
  using (<-well-founded)
open import Data.Fin.Dec
  using (_∈?_)
open import Relation.Nullary
  using (yes; no; ¬_)
open import Functions
  using (max)

module ScheduleDouble where

  record ScheduleDouble (n : ℕ) : Set where
    field
      {- α returns a subset of the shared memory elements that are active at time t -}
      α             : (t : 𝕋) → Subset n
      {- α returns the entire index set at time 0 -}
      α₀            : α 0 ≡ ⊤
      {- β returns the last time element i was accessed before time t -}
      β             : (t : 𝕋)(i j : Fin n) → 𝕋
      {- A1: Elements can only rely on their past values -}
      causality     : ∀ t i j → β (suc t) i j ≤ t
      {- A2: Each element gets updated infinitely often -}
      nonstarvation : ∀ t i → ∃ λ k →  (i ∈ (α (t + suc k)))
      {- A3: Each element will eventually not need its value at time t -}
      finite        : ∀ t i j → ∃ λ k → ∀ k₁ → β (t + k + k₁) i j ≢ t

  module Timing {n : ℕ}(s : ScheduleDouble n) where
    open ScheduleDouble s

    -- i ∈ α (t + suc k) → i ∈ α (suc t + k)
    ∈-α-comm : ∀ t k i → i ∈ α (t + suc k) → i ∈ α (suc t + k)
    ∈-α-comm t k i p = subst (i ∈_) (cong α (+-suc t k)) p

    -- nextActive' returns t+k given that i is accessed at time t+k
    nextActive' : (t k : 𝕋)(i : Fin n) → i ∈ α (t + suc k)
                  → Acc _<_ k → ∃ λ x → i ∈ α x
    nextActive' t zero    i p  _       = suc t ,
                subst (i ∈_) (cong α (trans (+-suc t 0) (cong suc (+-identityʳ t)))) p
    nextActive' t (suc k) i p (acc rs) with i ∈? α t
    ... | yes i∈α = t , i∈α
    ... | no  i∉α = nextActive' (suc t) k i (∈-α-comm t (suc k) i p)
        (rs k (≤-reflexive refl))

    -- nextActive returns a time after t, t', such that i is accessed at t'
    nextActive : 𝕋 → Fin n → 𝕋
    nextActive zero _ = 0
    nextActive (suc t) i with (nonstarvation (suc t) i)
    ... | (k , p) = proj₁ (nextActive' (suc t) k i p (<-well-founded k))

  
   

    -- expiryᵢⱼ returns a time such that i only uses data from j after time t
    expiryᵢⱼ : 𝕋 → Fin n → Fin n → 𝕋
    expiryᵢⱼ t i j = max {suc t} (λ x → (toℕ x) + proj₁ (finite (toℕ x) i j))

    -- expiryᵢ returns a time such that i only ever uses data from after time t
    expiryᵢ : 𝕋 → Fin n → 𝕋
    expiryᵢ t i = max (λ j → expiryᵢⱼ t i j)

    -- expiry returns a time such that all nodes only ever uses data from after time t
    expiry : 𝕋 → 𝕋
    expiry t = max (λ i → expiryᵢ t i)

    -- Definition of φ
    φ : 𝕋 → 𝕋
    φ zero    = zero
    φ (suc t) = suc (expiry (max {n} (λ i → nextActive (φ t) i)))
    
    -- Definition of τ
    τ : 𝕋 → Fin n → 𝕋
    τ t i = nextActive (φ t) i
