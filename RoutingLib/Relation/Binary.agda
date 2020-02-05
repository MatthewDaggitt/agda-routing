
module RoutingLib.Relation.Binary where

open import Data.Product
open import Function using (flip)
open import Relation.Binary
open import Relation.Nullary using (¬_)
open import Level

private
  variable
    a ℓ₁ ℓ₂ : Level
    A : Set a

--------------------------------------------------------------------------------
-- Minimums for strict orders

StrictMinimum : Rel A ℓ₁ → Rel A ℓ₂ → A → Set _
StrictMinimum _≈_ _<_ ⊥ = ∀ {x} → ¬ (x ≈ ⊥) → ⊥ < x 

StrictMaximum : Rel A ℓ₁ → Rel A ℓ₂ → A → Set _
StrictMaximum _≈_ _<_ ⊤ = ∀ {x} → ¬ (x ≈ ⊤) → x < ⊤
