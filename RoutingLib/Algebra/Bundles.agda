open import Algebra.Core
open import Level using (_⊔_; suc)
open import Relation.Binary

open import RoutingLib.Algebra.Structures

module RoutingLib.Algebra.Bundles where

record DecMagma c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier    : Set c
    _≈_        : Rel Carrier ℓ
    _∙_        : Op₂ Carrier
    isDecMagma : IsDecMagma _≈_ _∙_

  open IsDecMagma isDecMagma public

record DecMonoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier     : Set c
    _≈_         : Rel Carrier ℓ
    _∙_         : Op₂ Carrier
    ε           : Carrier
    isDecMonoid : IsDecMonoid _≈_ _∙_ ε

  open IsDecMonoid isDecMonoid public
