open import Algebra.FunctionProperties using (Op₂)
open import Data.List using ([]; _∷_; foldr; map; tabulate)
open import Data.List.Relation.Pointwise as PW using (Pointwise; []; _∷_)
open import Data.Fin using (Fin)
open import Function using (_∘_)
open import Relation.Binary using (REL; Rel; Reflexive; _⇒_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import RoutingLib.Data.List.Properties as Prop

module RoutingLib.Data.List.Relation.Pointwise where

-------------------------------------------------------------------
-- Reflexive properties

module _ {a ℓ} {A : Set a} {_~_ : Rel A ℓ} where

  reflexive-≡ : Reflexive _~_ → _≡_ ⇒ Pointwise _~_
  reflexive-≡ ref refl = PW.refl ref

module _ {a b ℓ} {A : Set a} {B : Set b} where

  foldr⁺ : ∀ (_~_ : REL A B ℓ) {_⊕ᵃ_ : Op₂ A} {_⊕ᵇ_ : Op₂ B} →
           (∀ {w x y z} → w ~ x → y ~ z → (w ⊕ᵃ y) ~ (x ⊕ᵇ z)) →
           ∀ {xs ys e f} → e ~ f → Pointwise _~_ xs ys →
           foldr _⊕ᵃ_ e xs ~ foldr _⊕ᵇ_ f ys
  foldr⁺ _ _    e~f []            = e~f
  foldr⁺ _ pres e~f (x~y ∷ xs~ys) = pres x~y (foldr⁺ _ pres e~f xs~ys)

  map-tabulate : ∀ {_~_ : Rel B ℓ} → Reflexive _~_ → ∀ {n} (f : A → B) (g : Fin n → A) →
                 Pointwise _~_ (map f (tabulate g)) (tabulate (f ∘ g))
  map-tabulate ref f g = reflexive-≡ ref (Prop.map-tabulate g f)
