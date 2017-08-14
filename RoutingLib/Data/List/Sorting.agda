open import Level using (_⊔_)
open import Data.List using (List; length; []; _∷_)
open import Relation.Binary using (DecTotalOrder; Rel)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Data.List.All using (AllPairs; []; _∷_)
open import RoutingLib.Data.List.Permutation using (_⇿_)
open import RoutingLib.Data.List.Uniqueness using (Unique)

module RoutingLib.Data.List.Sorting {a ℓ₁ ℓ₂} (order : DecTotalOrder a ℓ₁ ℓ₂) where

  open DecTotalOrder order renaming (Carrier to A)
  open Eq using () renaming (setoid to S)

  Sorted : List A → Set _
  Sorted xs = AllPairs _≤_ xs
  
  record _↗_ (xs ys : List A) : Set (a ⊔ ℓ₂) where
    constructor sorting
    field
      perm   : xs ⇿ ys
      sorted : Sorted ys
  



  module _ where

    postulate sort : List A → List A

    postulate sort-Sorted : ∀ xs → Sorted (sort xs)

    postulate sort-⇿ : ∀ xs → xs ⇿ sort xs
    
    sort-↗ : ∀ xs → xs ↗ (sort xs)
    sort-↗ xs = sorting (sort-⇿ xs) (sort-Sorted xs)
