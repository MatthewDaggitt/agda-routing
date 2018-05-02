open import Level using (_⊔_)
open import Data.List using (List; length; []; _∷_)
open import Relation.Binary using (Rel; DecTotalOrder)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Data.List.AllPairs using (AllPairs; []; _∷_)
open import RoutingLib.Data.List.Relation.Permutation using (_⇿_)
open import RoutingLib.Data.List.Uniqueness.Setoid using (Unique)

module RoutingLib.Data.List.Sorting {a ℓ} {A : Set a} (_≤_ : Rel A ℓ) where

  Sorted : List A → Set (a ⊔ ℓ)
  Sorted xs = AllPairs _≤_ xs
  
  record _↗_ (xs ys : List A) : Set (a ⊔ ℓ) where
    constructor sorting
    field
      perm   : xs ⇿ ys
      sorted : Sorted ys
