
open import Data.Maybe using (Maybe; nothing; just; Eq; drop-just)
open import Relation.Binary using (Rel; Reflexive; Symmetric; Transitive; Decidable; IsEquivalence; IsDecEquivalence; Setoid; DecSetoid; _⇒_)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)
open import Relation.Nullary using (¬_; yes; no)
open import Function using (_∘_)

module RoutingLib.Data.Maybe.Properties where

  just-injective : ∀ {a} {A : Set a} {x y : A} → (_≡_ {A = Maybe A}) (just x) (just y) → x ≡ y
  just-injective ≡-refl = ≡-refl
