open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Binary
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Relation.Binary

module RoutingLib.Relation.Binary.NonStrictToStrict
  {a ℓ₁ ℓ₂} {A : Set a} (_≈_ : Rel A ℓ₁) (_≤_ : Rel A ℓ₂)
  where

  open import Relation.Binary.NonStrictToStrict _≈_ _≤_

  <⇒≱ : Antisymmetric _≈_ _≤_ → ∀ {x y} → x < y → ¬ (y ≤ x)
  <⇒≱ antisym (x≤y , x≉y) y≤x = x≉y (antisym x≤y y≤x)

  ≤⇒≯ : Antisymmetric _≈_ _≤_ → ∀ {x y} → x ≤ y → ¬ (y < x)
  ≤⇒≯ antisym x≤y y<x = <⇒≱ antisym y<x x≤y

  ≰⇒> : Symmetric _≈_ → _≈_ ⇒ _≤_ → Total _≤_ →
        ∀ {x y} → ¬ (x ≤ y) → y < x
  ≰⇒> sym refl total {x} {y} x≰y with total x y
  ... | inj₁ x≤y = contradiction x≤y x≰y
  ... | inj₂ y≤x = y≤x , x≰y ∘ refl ∘ sym

  postulate ≮⇒≥ : ∀ {x y} → ¬ (x < y) → y ≤ x
