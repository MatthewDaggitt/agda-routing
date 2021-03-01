open import Relation.Binary hiding (Decidable)

open import Algebra.Core using (Op₂)
open import Data.List
import Data.List.Relation.Binary.Pointwise as Pointwise
open import Function.Base using (_∘_)
open import Relation.Unary

module RoutingLib.Data.List.Relation.Binary.Equality.Setoid
  {a ℓ} (S : Setoid a ℓ) where

open Setoid S renaming (Carrier to A)

open import Data.List.Relation.Binary.Equality.Setoid S hiding (filter⁺)

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
