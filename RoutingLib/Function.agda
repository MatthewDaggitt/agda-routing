open import Relation.Binary using (Rel)

module RoutingLib.Function
  {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
  (_≈₁_ : Rel A ℓ₁) -- Equality over the domain
  (_≈₂_ : Rel B ℓ₂) -- Equality over the codomain
  where

open import RoutingLib.Function.Definitions _≈₁_ _≈₂_ public
open import RoutingLib.Function.Structures  _≈₁_ _≈₂_ public
open import RoutingLib.Function.Packages public
