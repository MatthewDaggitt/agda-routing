open import Function.Bijection
open import Relation.Binary.PropositionalEquality

module RoutingLib.Function.Bijection where

infix 3 _⤖_

_⤖_ : ∀ {f t} → Set f → Set t → Set _
From ⤖ To = Bijection (setoid From) (setoid To)
