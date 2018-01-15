-- imports
open import Data.Nat using (ℕ; zero; suc; _≤_; _+_; _∸_)
open import Data.Fin using (Fin; toℕ; fromℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Subset using (Subset; ⊤; _∈_)
open import Data.Fin.Subset.Properties using (∈⊤)
open import Data.Product using (∃; _,_)
open import Relation.Binary.PropositionalEquality using (_≢_; refl; _≡_; sym; subst₂; trans; cong; subst; cong₂)
open import Data.Nat.Properties using (≤-reflexive; m≢1+m+n; +-suc; +-comm; +-assoc)
open import Function using (_∘_)

open Relation.Binary.PropositionalEquality.≡-Reasoning

open import RoutingLib.Asynchronous.Schedule

module RoutingLib.Asynchronous.Schedule.Synchronous where

  -- Synchronous Schedule functions
  α : {n : ℕ} → 𝕋 → Subset n
  α t = ⊤
  
  α₀ : {n : ℕ} → α {n} 0 ≡ ⊤
  α₀ = refl

  β : {n : ℕ} → 𝕋 → Fin n → Fin n → 𝕋
  β zero _ _ = zero
  β (suc t) _ _ = t
  
  causality : {n : ℕ} → ∀ t (i j : Fin n) → β (suc t) i j ≤ t
  causality t i j = ≤-reflexive refl

  nonstarvation : {n : ℕ} → ∀ t (i : Fin n) → ∃ λ k →  (i ∈ (α (t + suc k)))
  nonstarvation t i = zero , ∈⊤

  t+2+k≡ss-t+k : ∀ t k → t + 2 + k ≡ suc (suc (t + k))
  t+2+k≡ss-t+k t k = begin
    t + 2 + k ≡⟨ +-assoc t 2 k ⟩
    t + suc (suc k) ≡⟨ +-suc t (suc k) ⟩
    suc (t + suc k) ≡⟨ cong suc (+-suc t k) ⟩
    suc (suc (t + k)) ∎

  finite : {n : ℕ} → ∀ t (i j : Fin n)→ ∃ λ k → ∀ k₁ → β (t + k + k₁) i j ≢ t
  finite {n} t i j = 2 , λ k → subst (_≢ t)
         (sym (cong (λ x → β x i j) (t+2+k≡ss-t+k t k)))
         ((m≢1+m+n t) ∘ sym)

  -- Synchronous Schedule
  synchronous-schedule : (n : ℕ) → Schedule n
  synchronous-schedule n = record {
    α = α ;
    β = β ;
    causality = causality ;
    nonstarvation = nonstarvation ;
    finite = finite
    }
