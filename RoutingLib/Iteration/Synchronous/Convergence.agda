open import Data.Nat using (ℕ; zero; suc; _≤_; _+_; _∸_)
open import Data.Nat.Properties using (+-assoc; m+[n∸m]≡n)
open import Function using (_∘_)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality using (cong₂) renaming (sym to ≡-sym; refl to ≡-refl)
import Relation.Binary.EqReasoning as EqReasoning

open import RoutingLib.Iteration.Synchronous
import RoutingLib.Iteration.Synchronous.Properties as SyncProperties

module RoutingLib.Iteration.Synchronous.Convergence
  {a ℓ} (S : Setoid a ℓ) where

open Setoid S renaming (Carrier to A)
open EqReasoning S
open SyncProperties S

_ConvergesIn_ : (A → A) → ℕ → Set _
f ConvergesIn n = ∀ x t → (f ^ n) x ≈ (f ^ (n + t)) x

ConvergesIn-mono : ∀ f {n m} → n ≤ m → f ConvergesIn n → f ConvergesIn m
ConvergesIn-mono f {n} {m} n≤m conv x t = begin
  (f ^ m) x                   ≈⟨ ^-congʳ f (≡-sym (m+[n∸m]≡n n≤m)) x ⟩
  (f ^ (n + (m ∸ n))) x       ≈⟨ sym (conv x (m ∸ n)) ⟩
  (f ^ n) x                   ≈⟨ conv x (m ∸ n + t) ⟩
  (f ^ (n + ((m ∸ n) + t))) x ≈⟨ ^-congʳ f (≡-sym (+-assoc n (m ∸ n) t)) x ⟩
  (f ^ (n + (m ∸ n) + t)) x   ≈⟨ ^-congʳ f (cong₂ _+_ (m+[n∸m]≡n n≤m) ≡-refl) x ⟩
  (f ^ (m + t)) x ∎
