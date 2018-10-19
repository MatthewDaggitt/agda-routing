open import Data.Product
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function using (id)

module RoutingLib.Relation.Binary.PropositionalEquality where

isDecEquivalence : ∀ {a} {A : Set a} → Decidable (_≡_ {A = A}) → IsDecEquivalence (_≡_ {A = A})
isDecEquivalence _≟_ = record {
    isEquivalence = isEquivalence ;
    _≟_ = _≟_
  }


inspect′ : ∀ {a} {A : Set a} (x : A) → ∃ λ y → x ≡ y
inspect′ x = x , refl
