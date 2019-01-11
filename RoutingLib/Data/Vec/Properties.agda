open import Data.Vec
open import Relation.Nullary using (yes; no)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module RoutingLib.Data.Vec.Properties where

  ≡-dec : ∀ {a n} {A : Set a} → Decidable {A = A} _≡_ → Decidable {A = Vec A n} _≡_
  ≡-dec _≟_ []       []       = yes refl
  ≡-dec _≟_ (x ∷ xs) (y ∷ ys) with x ≟ y | ≡-dec _≟_ xs ys
  ... | yes refl | yes refl = yes refl
  ... | no  x≢y  | _        = no λ { refl → x≢y   refl }
  ... | _        | no xs≢ys = no λ { refl → xs≢ys refl }
