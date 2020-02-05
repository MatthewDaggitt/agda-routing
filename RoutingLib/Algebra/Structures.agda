
open import Level using (_⊔_)
open import Relation.Binary

module RoutingLib.Algebra.Structures {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) where

open import Algebra.Core using (Op₂)
open import Algebra.Structures _≈_

record IsDecMagma (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isMagma : IsMagma ∙
    _≟_     : Decidable _≈_

  open IsMagma isMagma public

record IsDecMonoid (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isMonoid : IsMonoid ∙ ε
    _≟_      : Decidable _≈_

  open IsMonoid isMonoid public

  isDecEquivalence : IsDecEquivalence _≈_
  isDecEquivalence = record
    { isEquivalence = isEquivalence
    ; _≟_           = _≟_
    }

  decSetoid : DecSetoid a ℓ
  decSetoid = record
    { isDecEquivalence = isDecEquivalence
    }
