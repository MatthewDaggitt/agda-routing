open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Function using (id; _∘_)
open import Relation.Binary using (Setoid; Rel)

module RoutingLib.Function.Iteration {a} {A : Set a} where

infix 7 _^ˡ_ _^ʳ_

_^ˡ_ : (A → A) → ℕ → (A → A)
f ^ˡ zero    = id
f ^ˡ (suc n) = f ∘ (f ^ˡ n)

_^ʳ_ : (A → A) → ℕ → (A → A)
f ^ʳ zero    = id
f ^ʳ (suc n) = (f ^ˡ n) ∘ f

FixedPoint : ∀ {ℓ} → Rel A ℓ → (A → A) → A → Set ℓ
FixedPoint _≈_ f x = f x ≈ x
