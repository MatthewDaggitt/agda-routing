open import Relation.Binary
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_; map)
open import Data.List.Relation.Binary.Permutation.Inductive using (_↭_; ↭-sym)
  renaming (refl to ↭-refl; trans to ↭-trans)
open import Data.Sum using (inj₁; inj₂)
import Data.List.Membership.Setoid as Membership

open import RoutingLib.Data.List using (insert)
open import RoutingLib.Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import RoutingLib.Data.List.Relation.Unary.All.Properties as All
open import RoutingLib.Data.List.Relation.Binary.Permutation.Inductive
import RoutingLib.Data.List.Sorting as Sorting
import RoutingLib.Data.List.Sorting.Properties as Sortingₚ
import RoutingLib.Data.List.Relation.Unary.Uniqueness.Setoid as Uniqueness
import RoutingLib.Data.List.Relation.Binary.Permutation.Inductive as Perm

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

  sort↭ : ∀ xs → sort xs ↭ xs
  sort↭ []       = ↭-refl
  sort↭ (x ∷ xs) = Perm.insert⁺ total x (sort↭ xs)

  sort!⁺ : ∀ {xs} → Unique xs → Unique (sort xs)
  sort!⁺ {xs} xs! = ↭-pres-! Eq.setoid (↭-sym (sort↭ xs)) xs!

  ∈-sort⁺ : ∀ {v xs} → v ∈ xs → v ∈ sort xs
  ∈-sort⁺ {_} {xs} v∈xs = ↭-pres-∈ Eq.setoid (↭-sym (sort↭ xs)) v∈xs

