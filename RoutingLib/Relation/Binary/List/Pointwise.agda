open import Relation.Binary hiding (Rel)
open import Relation.Binary.List.Pointwise hiding (refl)
open import Relation.Binary.PropositionalEquality
open import Data.List

module RoutingLib.Relation.Binary.List.Pointwise where

  ≡⇒Rel≈ : ∀ {a ℓ} {A : Set a} {_≈_ : REL A A ℓ} → Reflexive _≈_ → _≡_ ⇒ Rel _≈_
  ≡⇒Rel≈ ref {[]}     refl = []
  ≡⇒Rel≈ ref {x ∷ xs} refl = ref ∷ ≡⇒Rel≈ ref refl
