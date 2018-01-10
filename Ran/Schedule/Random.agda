-- imports
open import Schedule
  using (Schedule; 𝕋)
open import Data.Nat
  using (ℕ; zero; suc; _∸_; _≤_; _+_; s≤s)
open import Data.Fin
  using (Fin; toℕ)
open import Data.Product
  using (∃; _,_)
open import Data.Nat.Properties
  using (n∸m≤n; ≤-trans; n≤1+n; +-assoc; +-comm; +-suc; m+n∸n≡m; <⇒≢; m≤m+n; +-∸-comm; <⇒≤)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; subst; sym; trans; cong; cong₂; refl)
open import Function
  using (_∘_)
open import Data.Fin.Properties
  using (bounded)
open import Schedule.Synchronous
  using (α₀) renaming (α to α-sync; nonstarvation to nonstarvation-sync)
open import Schedule.RoundRobin
  using () renaming (α to α-rr; nonstarvation to nonstarvation-rr)

open Relation.Binary.PropositionalEquality.≡-Reasoning
  using (begin_; _≡⟨_⟩_; _∎)

module Schedule.Random {n}{l}(random : 𝕋 → Fin n → Fin l) where

  β :  𝕋 → Fin n → 𝕋
  β t i = t ∸ 1 ∸ toℕ (random t i)

  causality : ∀ t i → β (suc t) i ≤ t
  causality t i = n∸m≤n (toℕ (random (suc t) i)) t

  +-∸-assoc-fin : ∀ x y (i : Fin y) → x + y ∸ (toℕ i) ≡ x + (y ∸ (toℕ i))
  +-∸-assoc-fin x y i = begin
              x + y ∸ (toℕ i) ≡⟨ cong (_∸ (toℕ i)) (+-comm x y) ⟩
              y + x ∸ (toℕ i) ≡⟨ +-∸-comm x (<⇒≤ (bounded i)) ⟩
              (y ∸ toℕ i) + x ≡⟨ +-comm (y ∸ toℕ i) x ⟩
              x + (y ∸ (toℕ i)) ∎

  finite : ∀ t i → ∃ (λ k → ∀ k₁ → β (t + k + k₁) i ≢ t)
  finite t i = suc (suc l) , λ k → <⇒≢ (≤-trans
         (subst (suc t ≤_) (sym (+-suc t k)) (m≤m+n (suc t) k))
         (subst ((t + suc k) ≤_)
            (sym (trans
              (cong₂ β {u = i} (begin
                t + suc (suc l) + k ≡⟨ +-assoc t (suc (suc l)) k ⟩
                t + (suc (suc l) + k) ≡⟨ cong (t +_) (begin
                    suc (suc l) + k ≡⟨ +-comm (suc (suc l)) k ⟩
                    k + suc (suc l) ≡⟨ +-suc k (suc l) ⟩
                    suc (k + suc l) ≡⟨ cong suc (+-suc k l) ⟩
                    suc (suc k + l) ∎
                    ) ⟩
                t + suc (suc k + l) ≡⟨ +-suc t (suc k + l) ⟩
                  suc (t + (suc k + l)) ≡⟨ cong suc (sym (+-assoc t (suc k) l)) ⟩
                suc (t + suc k + l) ∎)
               refl)
              (+-∸-assoc-fin (t + suc k) l (random (suc (t + suc k + l)) i))))
            (m≤m+n (t + suc k) (l ∸ (toℕ (random (suc (t + suc k + l)) i)))))) ∘ sym

  latency-sync-schedule : Schedule n
  latency-sync-schedule = record {
    α = α-sync ;
    α₀ = α₀ ;
    β = β ;
    causality = causality ;
    nonstarvation = nonstarvation-sync;
    finite = finite
    }
