-- imports
open import Data.Nat using (ℕ; zero; suc; _≤_; _+_; _∸_)
open import Data.Product using (∃; _,_)
open import Data.Nat.Properties using (≤-reflexive; m≢1+m+n; +-suc; +-comm; +-assoc)
open import Function using (_∘_)
open import Level using () renaming (zero to 0ℓ)
open import Relation.Binary.PropositionalEquality using (_≢_; refl; _≡_; sym; subst₂; trans; cong; subst; cong₂)
open import Relation.Unary using (_∈_; U) renaming (Pred to Subset)
open import Relation.Unary.Properties using (U-Universal)

open Relation.Binary.PropositionalEquality.≡-Reasoning

open import RoutingLib.Asynchronous.Schedule

module RoutingLib.Asynchronous.Schedule.Synchronous {i} (I : Set i) where

  -- Synchronous Schedule functions
  α : 𝕋 → Subset I 0ℓ
  α t = U

  β : 𝕋 → I → I → 𝕋
  β zero _ _ = zero
  β (suc t) _ _ = t

  causality : ∀ t (i j : I) → β (suc t) i j ≤ t
  causality t i j = ≤-reflexive refl

  nonstarvation : ∀ t (i : I) → ∃ λ k → (i ∈ (α (t + suc k)))
  nonstarvation t i = zero , U-Universal t

  t+2+k≡ss-t+k : ∀ t k → t + 2 + k ≡ suc (suc (t + k))
  t+2+k≡ss-t+k t k = begin
    t + 2 + k ≡⟨ +-assoc t 2 k ⟩
    t + suc (suc k) ≡⟨ +-suc t (suc k) ⟩
    suc (t + suc k) ≡⟨ cong suc (+-suc t k) ⟩
    suc (suc (t + k)) ∎

  finite : ∀ t (i j : I)→ ∃ λ k → ∀ l → β (k + l) i j ≢ t
  finite t i j = t + 2 , λ k → subst (_≢ t)
         (sym (cong (λ x → β x i j) (t+2+k≡ss-t+k t k)))
         ((m≢1+m+n t) ∘ sym)

  -- Synchronous Schedule
  synchronous-schedule : Schedule I 0ℓ
  synchronous-schedule = record {
    α = α ;
    β = β ;
    causality = causality ;
    nonstarvation = nonstarvation ;
    finite = finite
    }
