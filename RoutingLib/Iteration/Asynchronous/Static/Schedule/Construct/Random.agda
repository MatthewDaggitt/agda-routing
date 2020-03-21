open import Data.Nat using (ℕ; zero; suc; _∸_; _≤_; _+_; s≤s)
open import Data.Fin using (Fin; toℕ)
open import RoutingLib.Iteration.Asynchronous.Static.Schedule

module RoutingLib.Iteration.Asynchronous.Static.Schedule.Construct.Random
  {n l} (random : 𝕋 → Fin n → Fin n → Fin l) where

open import Data.Product using (∃; _,_)
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Function using (_∘_)
open import Data.Fin.Properties using (toℕ<n)

open import RoutingLib.Iteration.Asynchronous.Static.Schedule.Construct.Synchronous
  using (αˢʸⁿᶜ)
open import RoutingLib.Iteration.Asynchronous.Static.Schedule.Construct.RoundRobin
  using (αʳʳ) renaming (nonstarvation to nonstarvation-rr)

open ≡-Reasoning

β :  𝕋 → Fin n → Fin n → 𝕋
β t i j = t ∸ 1 ∸ toℕ (random t i j)

causality : ∀ t i j → β (suc t) i j ≤ t
causality t i j = m∸n≤m t (toℕ (random (suc t) i j))

+-∸-assoc-fin : ∀ x y (i : Fin y) → x + y ∸ (toℕ i) ≡ x + (y ∸ (toℕ i))
+-∸-assoc-fin x y i = begin
  x + y ∸ (toℕ i)   ≡⟨ cong (_∸ (toℕ i)) (+-comm x y) ⟩
  y + x ∸ (toℕ i)   ≡⟨ +-∸-comm x (<⇒≤ (toℕ<n i)) ⟩
  (y ∸ toℕ i) + x   ≡⟨ +-comm (y ∸ toℕ i) x ⟩
  x + (y ∸ (toℕ i)) ∎

finite : ∀ t i j → ∃ (λ k → ∀ k' → β (k + k') i j ≢ t)
finite t i j = t + suc (suc l) , λ k → <⇒≢ (≤-trans
       (subst (suc t ≤_) (sym (+-suc t k)) (m≤m+n (suc t) k))
       (subst ((t + suc k) ≤_)
          (sym (trans
            (cong (λ x → β x i j) (begin
              t + suc (suc l) + k     ≡⟨ +-assoc t (suc (suc l)) k ⟩
              t + (suc (suc l) + k)   ≡⟨ cong (t +_) (push-suc k) ⟩
              t + suc (suc k + l)     ≡⟨ +-suc t (suc k + l) ⟩
              suc (t + (suc k + l))   ≡⟨ cong suc (sym (+-assoc t (suc k) l)) ⟩
              suc (t + suc k + l)     ∎))
            (+-∸-assoc-fin (t + suc k) l (random (suc (t + suc k + l)) i j))))
          (m≤m+n (t + suc k) (l ∸ (toℕ (random (suc (t + suc k + l)) i j)))))) ∘ sym
          where
          push-suc : ∀ k → suc (suc l) + k ≡ suc (suc k + l)
          push-suc k = begin
            suc (suc l) + k ≡⟨ +-comm (suc (suc l)) k ⟩
            k + suc (suc l) ≡⟨ +-suc k (suc l) ⟩
            suc (k + suc l) ≡⟨ cong suc (+-suc k l) ⟩
            suc (suc k + l) ∎

random-sync-schedule : Schedule n
random-sync-schedule = record
  { α             = αˢʸⁿᶜ
  ; β             = β
  ; β-causality   = causality
  }
