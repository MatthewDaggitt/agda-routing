open import Data.Maybe
open import Relation.Binary using (Rel; _⇒_; Reflexive)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module RoutingLib.Data.Maybe where

  Eq-reflexive : ∀ {a ℓ} {A : Set a} {_≈_ : Rel A ℓ} →
                 _≡_ ⇒ _≈_ → _≡_ ⇒ Eq _≈_
  Eq-reflexive reflexive refl = Eq-refl (reflexive refl)
