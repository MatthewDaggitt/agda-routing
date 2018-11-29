open import Data.Maybe
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Nullary using (yes; no)
import Relation.Nullary.Decidable as Dec

module RoutingLib.Data.Maybe.Relation.Cross where

data Cross {a b ℓ} {A : Set a} {B : Set b} (_∼_ : REL A B ℓ) :
           REL (Maybe A) (Maybe B) (a ⊔ b ⊔ ℓ) where
  nothingᵇ : Cross _∼_ nothing nothing
  nothingˡ : ∀ y → Cross _∼_ nothing (just y)
  nothingʳ : ∀ x → Cross _∼_ (just x) nothing
  just    : ∀ {x y} → x ∼ y → Cross _∼_ (just x) (just y)

module _ {a b ℓ} {A : Set a} {B : Set b} {_∼_ : REL A B ℓ} where

  dec : Decidable _∼_ → Decidable (Cross _∼_)
  dec _∼?_ nothing  nothing  = yes nothingᵇ
  dec _∼?_ nothing  (just y) = yes (nothingˡ y)
  dec _∼?_ (just x) nothing  = yes (nothingʳ x)
  dec _∼?_ (just x) (just y) with x ∼? y
  ... | yes x∼y = yes (just x∼y)
  ... | no ¬x∼y = no λ { (just x∼y) → ¬x∼y x∼y }
