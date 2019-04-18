open import Data.Nat using (ℕ; zero; suc; _∸_; _≤_; _+_; s≤s)

module RoutingLib.Iteration.Asynchronous.Static.Schedule.Construct.Delayed (l : ℕ) where

open import Data.Fin using (Fin)
open import Data.Nat.Properties using (n∸m≤n; <⇒≢; m+n∸n≡m; +-suc; m≤m+n; +-comm; +-assoc)
open import Data.Product using (∃; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≢_; _≡_; subst; cong; cong₂; refl; sym; trans; module ≡-Reasoning)
open import Function using (_∘_)

open ≡-Reasoning

open import RoutingLib.Iteration.Asynchronous.Static.Schedule
open import RoutingLib.Iteration.Asynchronous.Static.Schedule.Construct.RoundRobin
  using (αʳʳ) renaming (nonstarvation to nonstarvation-rr)
open import RoutingLib.Iteration.Asynchronous.Static.Schedule.Construct.Synchronous
  using (αˢʸⁿᶜ)

β : ∀ {n} → 𝕋 → Fin n → Fin n → 𝕋
β t i j = t ∸ 1 ∸ l

causality : ∀ {n} → ∀ t (i j : Fin n) → β (suc t) i j ≤ t
causality t i j = n∸m≤n l t

finite : ∀ {n} → ∀ t (i j : Fin n) → ∃ λ k → ∀ k' → β (k + k') i j ≢ t
finite t i j = t + suc (suc l) , λ k → subst (_≢ t)
  (sym (trans
    (cong (λ x → β x i j)
    (begin
      t + (2 + l) + k       ≡⟨ +-assoc t (suc (suc l)) k ⟩
      t + (2 + l + k)       ≡⟨ cong (t +_) (suc-push k) ⟩
      t + suc (suc k + l)   ≡⟨ +-suc t (suc k + l) ⟩
      suc (t + (suc k + l)) ≡⟨ cong suc (sym (+-assoc t (suc k) l)) ⟩
      suc (t + suc k + l)   ∎))
    (m+n∸n≡m (t + suc k) l)))
  ((<⇒≢ (subst (suc t ≤_) (sym (+-suc t k)) (s≤s (m≤m+n t k)))) ∘ sym)
  where
  suc-push : ∀ k → (2 + l) + k ≡ (2 + k) + l
  suc-push k = begin
    (2 + l) + k     ≡⟨ +-comm (suc (suc l)) k ⟩
    k + (2 + l)     ≡⟨ +-suc k (suc l) ⟩
    suc (k + suc l) ≡⟨ cong suc (+-suc k l) ⟩
    (2 + k) + l     ∎

latency-sync-schedule : (n : ℕ) → Schedule n
latency-sync-schedule n = record
  { α           = αˢʸⁿᶜ
  ; β           = β
  ; β-causality = causality
  }

latency-rr-schedule : (n : ℕ) → Schedule (suc n)
latency-rr-schedule n = record
  { α           = αʳʳ
  ; β           = β
  ; β-causality = causality
  }
