open import Data.Nat using (ℕ; zero; suc; _∸_; _≤_; _+_; s≤s)
open import Data.Fin using (Fin)
open import Data.Nat.Properties using (n∸m≤n; <⇒≢; m+n∸n≡m; +-suc; m≤m+n; +-comm; +-assoc)
open import Data.Product using (∃; _,_)
open import Relation.Binary.PropositionalEquality using (_≢_; _≡_; subst; cong; cong₂; refl; sym; trans)
open import Function using (_∘_)

open Relation.Binary.PropositionalEquality.≡-Reasoning
  using (begin_; _≡⟨_⟩_; _∎)

open import RoutingLib.Asynchronous.Schedule
open import RoutingLib.Asynchronous.Schedule.RoundRobin using () renaming (α to α-rr; nonstarvation to nonstarvation-rr)
open import RoutingLib.Asynchronous.Schedule.Synchronous using () renaming (α to α-sync; nonstarvation to nonstarvation-sync)

module RoutingLib.Asynchronous.Schedule.Latency (l : ℕ) where

  β : {n : ℕ} → 𝕋 → Fin n → Fin n → 𝕋
  β t _ _ = t ∸ 1 ∸ l 

  causality : {n : ℕ} → ∀ t (i j : Fin n) → β (suc t) i j ≤ t
  causality t i j = n∸m≤n l t

  finite : {n : ℕ} → ∀ t (i j : Fin n) → ∃ λ k → ∀ k₁ → β (t + k + k₁) i j ≢ t
  finite t i j = suc (suc l) , λ k → subst (_≢ t)
           (sym (trans
             (cong (λ x → β x i j)
             (begin
               t + suc (suc l) + k   ≡⟨ +-assoc t (suc (suc l)) k ⟩
               t + (suc (suc l) + k) ≡⟨ cong (t +_) (suc-push k) ⟩
               t + suc (suc k + l)   ≡⟨ +-suc t (suc k + l) ⟩
               suc (t + (suc k + l)) ≡⟨ cong suc (sym (+-assoc t (suc k) l)) ⟩
               suc (t + suc k + l)   ∎))
             (m+n∸n≡m (t + suc k) l)))
           ((<⇒≢ (subst (suc t ≤_) (sym (+-suc t k)) (s≤s (m≤m+n t k)))) ∘ sym)
           where
           suc-push : ∀ k → suc (suc l) + k ≡ suc (suc k + l)
           suc-push k = begin
             suc (suc l) + k   ≡⟨ +-comm (suc (suc l)) k ⟩
             k + suc (suc l)   ≡⟨ +-suc k (suc l) ⟩
             suc (k + suc l)   ≡⟨ cong suc (+-suc k l) ⟩
             suc (suc k + l)   ∎

  latency-sync-schedule : (n : ℕ) → Schedule n
  latency-sync-schedule n = record {
    α = α-sync ;
    β = β ;
    causality = causality ;
    nonstarvation = nonstarvation-sync;
    finite = finite
    }

  latency-rr-schedule : (n : ℕ) → Schedule (suc n)
  latency-rr-schedule n = record {
    α = α-rr ;
    β = β ;
    causality = causality ;
    nonstarvation = nonstarvation-rr;
    finite = finite
    }
  
