open import Algebra
open import Algebra.FunctionProperties using (Op₂)
open import Level using (_⊔_; suc)
open import Relation.Binary using (Rel)

open import RoutingLib.Algebra.Structures

module RoutingLib.Algebra where

-- stdlib
record Band c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    isBand  : IsBand _≈_ _∙_

  open IsBand isBand public

  semigroup : Semigroup c ℓ
  semigroup = record { isSemigroup = isSemigroup }

-- stdlib
record Semilattice c ℓ : Set (suc (c ⊔ ℓ)) where
  infixr 7 _∧_
  infix  4 _≈_
  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ
    _∧_           : Op₂ Carrier
    isSemilattice : IsSemilattice _≈_ _∧_

  open IsSemilattice isSemilattice public

  band : Band c ℓ
  band = record { isBand = isBand }

  open Band band public using (semigroup)
