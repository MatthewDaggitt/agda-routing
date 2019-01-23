
module RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.At where

open import Relation.Binary
open import Relation.Binary.Indexed.Homogeneous

------------------------------------------------------------------------
-- Structures

module _ {a i} {I : Set i} {A : I → Set a} where

  isEquivalence : ∀ {ℓ} {_≈_ : IRel A ℓ} → IsIndexedEquivalence A _≈_ →
                  (index : I) → IsEquivalence (_≈_ {index})
  isEquivalence isEq index = record
    { refl  = reflᵢ
    ; sym   = symᵢ
    ; trans = transᵢ
    }
    where open IsIndexedEquivalence isEq

  isPreorder : ∀ {ℓ₁ ℓ₂} {_≈_ : IRel A ℓ₁} {_∼_ : IRel A ℓ₂} →
               IsIndexedPreorder A _≈_ _∼_ →
               (index : I) → IsPreorder (_≈_ {index}) _∼_
  isPreorder isPreorder index = record
    { isEquivalence = isEquivalence O.isEquivalenceᵢ index
    ; reflexive     = O.reflexiveᵢ
    ; trans         = O.transᵢ
    }
    where module O = IsIndexedPreorder isPreorder

------------------------------------------------------------------------
-- Packages

module _ {a i} {I : Set i} where

  setoid : ∀ {ℓ} → IndexedSetoid I a ℓ → I → Setoid a ℓ
  setoid S index = record
    { Carrier       = S.Carrierᵢ index
    ; _≈_           = S._≈ᵢ_
    ; isEquivalence = isEquivalence S.isEquivalenceᵢ index
    }
    where module S = IndexedSetoid S

  preorder : ∀ {ℓ₁ ℓ₂} → IndexedPreorder I a ℓ₁ ℓ₂ → I → Preorder a ℓ₁ ℓ₂
  preorder O index = record
    { Carrier    = O.Carrierᵢ index
    ; _≈_        = O._≈ᵢ_
    ; _∼_        = O._∼ᵢ_
    ; isPreorder = isPreorder O.isPreorderᵢ index
    }
    where module O = IndexedPreorder O


------------------------------------------------------------------------
-- Some useful shorthand infix notation

module _ {a i} {I : Set i} where

  _atₛ_ : ∀ {ℓ} → IndexedSetoid I a ℓ → I → Setoid a ℓ
  _atₛ_ = setoid
