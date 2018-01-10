open import Data.List using (List; []; _∷_; length; splitAt)
open import Data.Nat using (⌈_/2⌉)
open import Data.Product using (_,_)
open import Relation.Binary using (DecTotalOrder)

open import RoutingLib.Data.List using (merge)

module RoutingLib.Data.List.Sorting.Mergesort {a ℓ₁ ℓ₂} (DTO : DecTotalOrder a ℓ₁ ℓ₂) where

  open DecTotalOrder DTO renaming (Carrier to A)

  mergesort : List A → List A
  mergesort []       = []
  mergesort (x ∷ xs) with splitAt ⌈ length (x ∷ xs) /2⌉ (x ∷ xs)
  ... | ls , rs = merge total {!mergesort ls!} {!!}
  
