open import Data.List using ([]; _∷_)
open import Relation.Binary using (Rel; Reflexive; _⇒_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.List.Pointwise using ([]; _∷_) renaming (Rel to PW)

module RoutingLib.Data.List.Relation.Pointwise where

  ≡⇒Rel≈ : ∀ {a ℓ} {A : Set a} {_≈_ : Rel A ℓ} → Reflexive _≈_ → _≡_ ⇒ PW _≈_
  ≡⇒Rel≈ ref {[]}     refl = []
  ≡⇒Rel≈ ref {x ∷ xs} refl = ref ∷ ≡⇒Rel≈ ref refl
