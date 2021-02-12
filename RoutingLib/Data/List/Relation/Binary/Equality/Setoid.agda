open import Relation.Binary hiding (Decidable)

module RoutingLib.Data.List.Relation.Binary.Equality.Setoid
  {a ℓ} (S : Setoid a ℓ) where

open import Algebra.Core using (Op₂)
open import Data.Fin using (Fin)
open import Data.List
import Data.List.Relation.Binary.Equality.Setoid as SetoidEquality hiding (filter⁺)
import Data.List.Relation.Binary.Pointwise as Pointwise
open import Function using (_∘_)
open import Relation.Unary

import RoutingLib.Data.List.Relation.Binary.Pointwise as PW

open Pointwise public using (head; tail)

open Setoid S renaming (Carrier to A)
open SetoidEquality S

--stdlib
foldr⁺ : ∀ {_•_ : Op₂ A} {_◦_ : Op₂ A} →
         (∀ {w x y z} → w ≈ x → y ≈ z → (w • y) ≈ (x ◦ z)) →
         ∀ {xs ys e f} → e ≈ f → xs ≋ ys →
         foldr _•_ e xs ≈ foldr _◦_ f ys
foldr⁺ _    e~f []            = e~f
foldr⁺ pres e~f (x~y ∷ xs~ys) = pres x~y (foldr⁺ pres e~f xs~ys)

module _ {p q} {P : Pred A p} {Q : Pred A q}
         (P? : Decidable P) (Q? : Decidable Q)
         (P⇒Q : ∀ {a b} → a ≈ b → P a → Q b)
         (Q⇒P : ∀ {a b} → a ≈ b → Q b → P a)
         where

  filter⁺ : ∀ {as bs} → as ≋ bs → filter P? as ≋ filter Q? bs
  filter⁺ = Pointwise.filter⁺ P? Q? P⇒Q Q⇒P
