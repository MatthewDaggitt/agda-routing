open import Algebra.FunctionProperties
open import Level using (_⊔_; suc)
open import Relation.Binary

open import RoutingLib.Algebra.Structures

module RoutingLib.Algebra where

record Magma c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    isMagma : IsMagma _≈_ _∙_

  open IsMagma isMagma public
