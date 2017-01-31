
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module RoutingLib.Relation.Binary.PropositionalEquality where

  isDecEquivalence : ∀ {a} {A : Set a} → Decidable (_≡_ {A = A}) → IsDecEquivalence (_≡_ {A = A})
  isDecEquivalence _≟_ = record {
      isEquivalence = isEquivalence ;
      _≟_ = _≟_
    }
