open import Level using (_⊔_)
open import Data.List using (List; length; []; _∷_)
open import Relation.Binary using (Rel; DecTotalOrder)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import RoutingLib.Data.List.Relation.Unary.Uniqueness.Setoid using (Unique)

module RoutingLib.Data.List.Sorting {a ℓ} {A : Set a} (_≤_ : Rel A ℓ) where

  Sorted : List A → Set (a ⊔ ℓ)
  Sorted xs = AllPairs _≤_ xs
