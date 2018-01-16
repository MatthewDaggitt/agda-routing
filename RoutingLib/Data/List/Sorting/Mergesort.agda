open import Data.List using (List; []; _∷_; length; splitAt)
import Data.List.Any.Membership as Membership
open import Data.List.All using (All)
open import Data.Nat using (⌈_/2⌉)
open import Data.Product using (_,_)
open import Relation.Binary using (DecTotalOrder)
open import Relation.Unary using (Pred)

open import RoutingLib.Data.List using (merge)
open import RoutingLib.Data.List.Sorting using (Sorted)
open import RoutingLib.Data.List.Uniqueness.Setoid using (Unique)

module RoutingLib.Data.List.Sorting.Mergesort {a ℓ₁ ℓ₂} (DTO : DecTotalOrder a ℓ₁ ℓ₂) where

  open DecTotalOrder DTO renaming (Carrier to A)
  open Eq renaming (setoid to S)
  open Membership S using (_∈_)
  
  postulate mergesort : List A → List A

  postulate mergesort↗ : ∀ xs → Sorted DTO (mergesort xs)
  
  postulate mergesort!⁺ : ∀ {xs} → Unique S xs → Unique S (mergesort xs)

  postulate mergesort!⁻ : ∀ {xs} → Unique S (mergesort xs) → Unique S xs
  
  postulate ∈-mergesort⁺ : ∀ {x xs} → x ∈ xs → x ∈ mergesort xs

  postulate ∈-mergesort⁻ : ∀ {x xs} → x ∈ mergesort xs → x ∈ xs

  postulate All-mergesort⁺ : ∀ {p} (P : Pred A p) {xs} → All P xs → All P (mergesort xs)
  
  --postulate mergesort :


  {-
  mergesort []       = []
  mergesort (x ∷ xs) with splitAt ⌈ length (x ∷ xs) /2⌉ (x ∷ xs)
  ... | ls , rs = merge total {!mergesort ls!} {!!}
  -}
