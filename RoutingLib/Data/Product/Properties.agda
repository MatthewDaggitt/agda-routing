
open import Data.Product
open import Relation.Binary.PropositionalEquality

module RoutingLib.Data.Product.Properties where

module _ {a b} {A : Set a} {B : Set b} where

  -- stdlib
  ,-injective : ∀ {a c : A} {b d : B} → (a , b) ≡ (c , d) → a ≡ c × b ≡ d
  ,-injective refl = refl , refl
