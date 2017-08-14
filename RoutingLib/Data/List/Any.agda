open import Relation.Binary using (REL)
open import Data.List using (List; _∷_)
open import Data.List.Any using (Any; here; there)

module RoutingLib.Data.List.Any where


  data Any₂ {a b ℓ} {A : Set a} {B : Set b} (_~_ : REL A B ℓ) : REL (List A) (List B) ℓ where
    here  : ∀ {x y xs ys} → x ~ y          → Any₂ _~_ (x ∷ xs) (y ∷ ys)
    there : ∀ {x y xs ys} → Any₂ _~_ xs ys → Any₂ _~_ (x ∷ xs) (y ∷ ys)


