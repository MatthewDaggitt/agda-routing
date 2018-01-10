module Schedule where

  -- imports
  open import Data.Nat
    using (ℕ; zero; suc; _≤_; _<_; _+_; _≤?_)
  open import Data.Fin
    using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
  open import Data.Fin.Subset
    using (Subset; _∈_; ⊤)
  open import Data.Product
    using (∃; _,_; proj₁; _×_)
  open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; subst₂; cong; subst; sym; trans)
  open import Induction.WellFounded
    using (Acc; acc)
  open import Data.Nat.Properties
    using (≤-reflexive; +-suc; +-identityʳ)
  open import Induction.Nat
    using (<-well-founded)
  open import Functions
    using (max)
  open import Data.Fin.Dec
    using (_∈?_)
  open import Relation.Nullary
    using (yes; no; Dec; ¬_)
  open import Relation.Nullary.Product
    using (_×-dec_)
  open import Data.Fin.Subset.Properties
    using (∈⊤)

  -- Timestamps
  𝕋 : Set
  𝕋 = ℕ

  -- Schedule
  record Schedule (n : ℕ) : Set where
    field
      {- α returns a subset of the shared memory elements that are active at time t -}
      α             : (t : 𝕋) → Subset n
      {- α returns the entire index set at time 0 -}
      α₀            : α 0 ≡ ⊤
      {- β returns the last time element i was accessed before time t -}
      β             : (t : 𝕋)(i : Fin n) → 𝕋
      {- A1: Elements can only rely on their past values -}
      causality     : ∀ t i → β (suc t) i ≤ t
      {- A2: Each element gets updated infinitely often -}
      nonstarvation : ∀ t i → ∃ λ k →  (i ∈ (α (t + suc k)))
      {- A3: Each element will eventually not need its value at time t -}
      finite        : ∀ t i → ∃ λ k → ∀ k₁ → β (t + k + k₁) i ≢ t


  -- Functions related to schedules
  module Timing {n : ℕ}(s : Schedule n) where
    open Schedule s
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

    -- expiry returns a time k such that element i does not rely on any time before t
    expiry : 𝕋 → Fin n → 𝕋
    expiry t i = max {suc t} (λ x → (toℕ x) + proj₁ (finite (toℕ x) i))

    -- Definition of φ
    φ :  𝕋 → 𝕋
    φ zero    = zero
    φ (suc t) = suc (max {n} (λ i → expiry (nextActive (φ t) i) i))

    -- Definition of τ
    τ : 𝕋 → Fin n → 𝕋
    τ t i = nextActive (φ t) i
