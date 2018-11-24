open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; _∈_; ⊤)
open import Data.Fin.Subset.Properties using (∈⊤)
open import Data.Nat using (ℕ; zero; suc; _≤_; _+_; _∸_)
open import Data.Nat.Properties using (≤-reflexive; m≢1+m+n; +-suc; +-comm; +-assoc)
open import Data.Product using (∃; _,_)
open import Function using (_∘_)
open import Level using () renaming (zero to 0ℓ)
open import Relation.Binary.PropositionalEquality using (_≢_; refl; _≡_; sym; subst₂; trans; cong; subst; cong₂; module ≡-Reasoning)
open import Relation.Unary.Properties using (U-Universal)

open import RoutingLib.Asynchronous.Schedule

open ≡-Reasoning

module RoutingLib.Asynchronous.Schedule.Synchronous {n : ℕ} where

  -- Synchronous Schedule functions
  α : 𝕋 → Subset n
  α t = ⊤

  β : 𝕋 → Fin n → Fin n → 𝕋
  β zero _ _ = zero
  β (suc t) _ _ = t

  causality : ∀ t (i j : Fin n) → β (suc t) i j ≤ t
  causality t i j = ≤-reflexive refl

  nonstarvation : ∀ t (i : Fin n) → ∃ λ k → (i ∈ (α (t + suc k)))
  nonstarvation t i = zero , ∈⊤

  t+2+k≡ss-t+k : ∀ t k → t + 2 + k ≡ suc (suc (t + k))
  t+2+k≡ss-t+k t k = begin
    t + 2 + k         ≡⟨ +-assoc t 2 k ⟩
    t + suc (suc k)   ≡⟨ +-suc t (suc k) ⟩
    suc (t + suc k)   ≡⟨ cong suc (+-suc t k) ⟩
    suc (suc (t + k)) ∎

  finite : ∀ t (i j : Fin n)→ ∃ λ k → ∀ l → β (k + l) i j ≢ t
  finite t i j = t + 2 , λ k → subst (_≢ t)
         (sym (cong (λ x → β x i j) (t+2+k≡ss-t+k t k)))
         ((m≢1+m+n t) ∘ sym)

  -- Synchronous Schedule
  synchronous-schedule : Schedule n
  synchronous-schedule = record {
    α = α ;
    β = β ;
    causality = causality ;
    nonstarvation = nonstarvation ;
    finite = finite
    }
