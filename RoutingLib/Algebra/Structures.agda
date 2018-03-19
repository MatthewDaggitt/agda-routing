open import Algebra.Structures
open import Algebra.FunctionProperties
open import Level using (_⊔_)
open import Relation.Binary using (Rel)

module RoutingLib.Algebra.Structures {a ℓ} {A : Set a} (≈ : Rel A ℓ) where

  record IsChoiceSemigroup (• : Op₂ A) : Set (a ⊔ ℓ) where
    field
      isSemigroup : IsSemigroup ≈ •
      comm        : Commutative ≈ •
      sel         : Selective   ≈ •
      
