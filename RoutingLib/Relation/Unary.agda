
open import Data.Product using (_×_)
open import Relation.Unary
open import Relation.Nullary using (¬_)

module RoutingLib.Relation.Unary {a} {A : Set a} where

  -----------------------
  -- To push to stdlib --
  -----------------------

  _Preserves_ : ∀ {a p} {A : Set a} → (A → A) → Pred A p → Set _
  f Preserves P = ∀ {a} → P a → P (f a)

  _Forces_ : ∀ {a p} {A : Set a} → (A → A) → Pred A p → Set _
  f Forces P = ∀ {a} → P (f a) → P a



  -----------
  -- Other --
  -----------

  infix 4 _⊈_ _⊂_
  
  _⊈_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
  P ⊈ Q = ¬ (P ⊆ Q)

  _⊂_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
  P ⊂ Q = P ⊆ Q × Q ⊈ P
