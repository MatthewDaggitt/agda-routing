open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Product using (∃)
open import Function using (id; _∘_)
open import Level using (_⊔_)
open import Relation.Binary using (Setoid; Rel; _Preserves_⟶_)
open import Relation.Unary using (Pred; _∈_; U)

module RoutingLib.Iteration.Synchronous {a} {A : Set a} where

infixl 7 _^_

_^_ : (A → A) → ℕ → (A → A)
f ^ zero    = id
f ^ (suc n) = f ∘ (f ^ n)

module _ {ℓ} (_≈_ : Rel A ℓ) (f : A → A) where

  IsFixedPoint : A → Set ℓ
  IsFixedPoint x = f x ≈ x

  ConvergesOver : ∀ {p} → Pred A p → Set (a ⊔ ℓ ⊔ p)
  ConvergesOver P = ∀ {x} → x ∈ P → ∃ λ t → IsFixedPoint ((f ^ (suc t)) x)

  Converges : Set (a ⊔ ℓ)
  Converges = ConvergesOver U
