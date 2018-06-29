open import Relation.Binary
open import Data.List using (List; []; _∷_)
open import Data.List.All using ([]; _∷_; map)
open import Data.Sum using (inj₁; inj₂)
import Data.List.Membership.Setoid as Membership

open import RoutingLib.Data.List using (insert)
open import RoutingLib.Data.List.AllPairs using ([]; _∷_)
open import RoutingLib.Data.List.All.Properties as All
open import RoutingLib.Data.List.Relation.Permutation
open import RoutingLib.Data.List.Relation.Permutation.Properties
open import RoutingLib.Data.List.Uniqueness.Setoid.Properties using (perm!)
open import RoutingLib.Data.List.Membership.Setoid.Properties using (∈-perm)
import RoutingLib.Data.List.Sorting as Sorting
import RoutingLib.Data.List.Sorting.Properties as Sortingₚ
import RoutingLib.Data.List.Uniqueness.Setoid as Uniqueness


module RoutingLib.Data.List.Sorting.InsertionSort
  {a ℓ₁ ℓ₂} (decTotalOrder : DecTotalOrder a ℓ₁ ℓ₂) where

  open DecTotalOrder decTotalOrder renaming (Carrier to A)
  open Sorting _≤_
  open Sortingₚ decTotalOrder
  open Uniqueness Eq.setoid using (Unique)
  open Membership Eq.setoid using (_∈_)
  
  sort : List A → List A
  sort []       = []
  sort (x ∷ xs) = insert total x (sort xs)

  sort↗ : ∀ xs → Sorted (sort xs)
  sort↗ []       = []
  sort↗ (x ∷ xs) = insert↗⁺ x (sort↗ xs)

  sort⇿ : ∀ xs → sort xs ⇿ xs
  sort⇿ []       = []
  sort⇿ (x ∷ xs) = ⇿-insert⁺ total x (sort⇿ xs)

  sort!⁺ : ∀ {xs} → Unique xs → Unique (sort xs)
  sort!⁺ {xs} xs! = perm! Eq.setoid xs! (⇿-sym (sort⇿ xs))

  ∈-sort⁺ : ∀ {v xs} → v ∈ xs → v ∈ sort xs
  ∈-sort⁺ {_} {xs} v∈xs = ∈-perm Eq.setoid v∈xs (⇿-sym (sort⇿ xs))

