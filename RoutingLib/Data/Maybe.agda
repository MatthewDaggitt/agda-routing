open import Data.Maybe
open import Level using (_⊔_)
open import Relation.Binary using (Rel; REL; _⇒_; Reflexive)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module RoutingLib.Data.Maybe where

  Eq-reflexive : ∀ {a ℓ} {A : Set a} {_≈_ : Rel A ℓ} →
                 _≡_ ⇒ _≈_ → _≡_ ⇒ Eq _≈_
  Eq-reflexive reflexive refl = Eq-refl (reflexive refl)


  Eq' : ∀ {a ℓ} {A : Set a} → Rel A ℓ → REL (Maybe A) A (a ⊔ ℓ)
  Eq' _~_ x y = Any (_~ y) x
