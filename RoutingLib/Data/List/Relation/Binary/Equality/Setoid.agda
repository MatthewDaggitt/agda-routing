open import Algebra.FunctionProperties using (Op₂)
open import Data.Fin using (Fin)
open import Data.List using (foldr; map; tabulate)
import Data.List.Relation.Equality.Setoid as SetoidEquality
open import Function using (_∘_)
open import Relation.Binary

import RoutingLib.Data.List.Relation.Binary.Pointwise as PW

module RoutingLib.Data.List.Relation.Binary.Equality.Setoid where

module _ {a ℓ} (S : Setoid a ℓ) where

  open Setoid S renaming (Carrier to A)
  open SetoidEquality S

  foldr⁺ : ∀ {_•_ : Op₂ A} {_◦_ : Op₂ A} →
           (∀ {w x y z} → w ≈ x → y ≈ z → (w • y) ≈ (x ◦ z)) →
           ∀ {xs ys e f} → e ≈ f → xs ≋ ys →
           foldr _•_ e xs ≈ foldr _◦_ f ys
  foldr⁺ _    e~f []            = e~f
  foldr⁺ pres e~f (x~y ∷ xs~ys) = pres x~y (foldr⁺ pres e~f xs~ys)

  map-tabulate : ∀ {b} {B : Set b} {n} (f : B → A) (g : Fin n → B) →
                 map f (tabulate g) ≋ tabulate (f ∘ g)
  map-tabulate = PW.map-tabulate refl
