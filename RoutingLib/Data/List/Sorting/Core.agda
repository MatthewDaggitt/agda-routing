
open import Relation.Binary

module RoutingLib.Data.List.Sorting.Core
  {a ℓ₁ ℓ₂} (totalOrder : TotalOrder a ℓ₁ ℓ₂) where

open TotalOrder totalOrder
  renaming (Carrier to A)

open import Data.List.Base
open import Data.List.Relation.Binary.Permutation.Setoid Eq.setoid
open import Level using (_⊔_)

open import RoutingLib.Data.List.Relation.Unary.Sorted totalOrder


record SortingAlgorithm : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    sort   : List A → List A
    sort-↭ : ∀ xs → sort xs ↭ xs
    sort-↗ : ∀ xs → Sorted (sort xs)
