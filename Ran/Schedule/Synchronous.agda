module Schedule.Synchronous where

  -- imports
  open import Schedule
    using (Schedule; 𝕋)
  open import Data.Nat
    using (ℕ; zero; suc; _≤_; _+_; _∸_)
  open import Data.Fin
    using (Fin; toℕ; fromℕ) renaming (zero to fzero; suc to fsuc)
  open import Data.Fin.Subset
    using (Subset; ⊤; _∈_)
  open import Data.Fin.Subset.Properties
    using (∈⊤)
  open import Data.Product
    using (∃; _,_)
  open import Relation.Binary.PropositionalEquality
    using (_≢_; refl; _≡_; sym; subst₂; trans; cong; subst; cong₂)
  open import Data.Nat.Properties
    using (≤-reflexive; m≢1+m+n; +-suc; +-comm; +-assoc)
  open import Function
    using (_∘_)
  open import Data.Vec
    using (Vec; tabulate; lookup; _∷_)

  open Relation.Binary.PropositionalEquality.≡-Reasoning
    using (begin_; _≡⟨_⟩_; _∎)

  -- Synchronous Schedule functions
  α : {n : ℕ} → 𝕋 → Subset n
  α t = ⊤
  
  α₀ : {n : ℕ} → α {n} 0 ≡ ⊤
  α₀ = refl

  β : {n : ℕ} → 𝕋 → Fin n → 𝕋
  β zero _ = zero
  β (suc t) _ = t
  
  causality : {n : ℕ} → ∀ t (i : Fin n) → β (suc t) i ≤ t
  causality t i = ≤-reflexive refl

  nonstarvation : {n : ℕ} → ∀ t (i : Fin n) → ∃ λ k →  (i ∈ (α (t + suc k)))
  nonstarvation t i = zero , ∈⊤

  t+2+k≡ss-t+k : ∀ t k → t + 2 + k ≡ suc (suc (t + k))
  t+2+k≡ss-t+k t k = begin
    t + 2 + k ≡⟨ +-assoc t 2 k ⟩
    t + suc (suc k) ≡⟨ +-suc t (suc k) ⟩
    suc (t + suc k) ≡⟨ cong suc (+-suc t k) ⟩
    suc (suc (t + k)) ∎

  finite : {n : ℕ} → ∀ t (i : Fin n) → ∃ λ k → ∀ k₁ → β (t + k + k₁) i ≢ t
  finite {n} t i = 2 , λ k → subst (_≢ t)
         (sym ((cong₂ β {u = i}
           (t+2+k≡ss-t+k t k)
           refl)))
         ((m≢1+m+n t) ∘ sym)

  -- Synchronous Schedule
  synchronous-schedule : (n : ℕ) → Schedule n
  synchronous-schedule n = record {
    α = α ;
    α₀ = α₀ ;
    β = β ;
    causality = causality ;
    nonstarvation = nonstarvation ;
    finite = finite
    }

  -- Bounds Measurements
  -- module Bounds (n : ℕ) where
  schedule : Schedule 20
  schedule = synchronous-schedule 20

  open Schedule.Timing schedule

  x : Vec 𝕋 10
  x = tabulate (λ i → φ (toℕ i))
  
  a : Fin 10
  a = fsuc (fsuc (fsuc (fsuc fzero)))
