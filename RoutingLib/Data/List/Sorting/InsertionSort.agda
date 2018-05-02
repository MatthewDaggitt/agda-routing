open import Relation.Binary
open import Data.List using (List; []; _∷_)
open import Data.List.All using ([]; _∷_; map)
open import Data.Sum using (inj₁; inj₂)

open import RoutingLib.Data.List using (insert)
open import RoutingLib.Data.List.AllPairs using ([]; _∷_)
open import RoutingLib.Data.List.All.Properties as All
open import RoutingLib.Data.List.Permutation
open import RoutingLib.Data.List.Permutation.Properties
import RoutingLib.Data.List.Sorting as Sorting
import RoutingLib.Data.List.Sorting.Properties as Sortingₚ

module RoutingLib.Data.List.Sorting.InsertionSort
  {a ℓ₁ ℓ₂} (decTotalOrder : DecTotalOrder a ℓ₁ ℓ₂) where

  open DecTotalOrder decTotalOrder renaming (Carrier to A)
  open Sorting _≤_
  open Sortingₚ decTotalOrder
  
  sort : List A → List A
  sort []       = []
  sort (x ∷ xs) = insert total x (sort xs)

  sort↗ : ∀ xs → Sorted (sort xs)
  sort↗ []       = []
  sort↗ (x ∷ xs) = insert↗⁺ x (sort↗ xs)

  sort⇿ : ∀ xs → sort xs ⇿ xs
  sort⇿ []       = []
  sort⇿ (x ∷ xs) = ⇿-insert⁺ total x (sort⇿ xs)
