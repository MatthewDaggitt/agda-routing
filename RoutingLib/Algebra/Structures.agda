open import Algebra.Structures
open import Algebra.FunctionProperties
open import Level using (_⊔_)
open import Relation.Binary using (Rel)

module RoutingLib.Algebra.Structures {a ℓ} {A : Set a} (≈ : Rel A ℓ) where

-- stdlib
record IsBand (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isSemigroup : IsSemigroup ≈ ∙
    idem        : Idempotent ≈ ∙

  open IsSemigroup isSemigroup public

-- stdlib
record IsSemilattice (∧ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isBand : IsBand ∧
    comm   : Commutative ≈ ∧

  open IsBand isBand public
