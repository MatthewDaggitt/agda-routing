
open import Level using (_⊔_)
open import Relation.Binary

module RoutingLib.Algebra.Structures {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) where

open import Algebra.FunctionProperties _≈_


record IsMagma (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isEquivalence : IsEquivalence _≈_
    ∙-cong        : Congruent₂ ∙

  open IsEquivalence isEquivalence public

  setoid : Setoid a ℓ
  setoid = record { isEquivalence = isEquivalence }
