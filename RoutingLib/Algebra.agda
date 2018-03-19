open import Algebra.FunctionProperties using (Op₂)
open import Level using (_⊔_; suc)
open import Relation.Binary using (Rel)

open import RoutingLib.Algebra.Structures

module RoutingLib.Algebra where

  {-
  record SelectiveSemigroup c ℓ : Set (suc (c ⊔ ℓ)) where
    field
      Carrier              : Set c
      _≈_                  : Rel Carrier ℓ
      _•_                  : Op₂ Carrier
      isSelectiveSemigroup : IsSelectiveSemigroup _≈_ _•_
  -}
  
  record ChoiceSemigroup c ℓ : Set (suc (c ⊔ ℓ)) where
    field
      Carrier           : Set c
      _≈_               : Rel Carrier ℓ
      _•_               : Op₂ Carrier
      isChoiceSemigroup : IsChoiceSemigroup _≈_ _•_
