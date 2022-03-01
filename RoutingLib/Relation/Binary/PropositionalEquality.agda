
module RoutingLib.Relation.Binary.PropositionalEquality where

open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

private
  variable
    a : Level
    A : Set a

-- stdlib v2.0
isPartialOrder : IsPartialOrder {A = A} _≡_ _≡_
isPartialOrder = record
  { isPreorder = isPreorder
  ; antisym    = λ eq _ → eq
  }

-- stdlib v2.0
poset : Set a → Poset _ _ _
poset A = record
  { Carrier        = A
  ; _≈_            = _≡_
  ; _≤_            = _≡_
  ; isPartialOrder = isPartialOrder
  }
