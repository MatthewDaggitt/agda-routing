open import Relation.Binary

module RoutingLib.Data.List.Sorting.InsertionSort
  {a ℓ₁ ℓ₂} (decTotalOrder : DecTotalOrder a ℓ₁ ℓ₂) where

open DecTotalOrder decTotalOrder renaming (Carrier to A)

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_; map)
open import Data.List.Relation.Binary.Permutation.Setoid Eq.setoid
open import Data.List.Relation.Binary.Permutation.Setoid.Properties Eq.setoid using (Unique-resp-↭; ∈-resp-↭)
open import Data.List.Relation.Binary.Equality.Setoid Eq.setoid using (_≋_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
import Data.List.Relation.Unary.Unique.Setoid as Uniqueness
open import Data.Sum using (inj₁; inj₂)
import Data.List.Membership.Setoid as Membership

open import RoutingLib.Data.List using (insert)
open import RoutingLib.Data.List.Relation.Unary.All.Properties as All hiding (insert⁺)
open import RoutingLib.Data.List.Relation.Binary.Permutation.Setoid.Properties Eq.setoid
import RoutingLib.Data.List.Sorting as Sorting
import RoutingLib.Data.List.Sorting.Properties as Sortingₚ

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
sort↭ (x ∷ xs) = insert⁺ total x (sort↭ xs)

sort!⁺ : ∀ {xs} → Unique xs → Unique (sort xs)
sort!⁺ {xs} xs! = Unique-resp-↭ (↭-sym (sort↭ xs)) xs!

∈-sort⁺ : ∀ {v xs} → v ∈ xs → v ∈ sort xs
∈-sort⁺ {_} {xs} v∈xs = ∈-resp-↭ (↭-sym (sort↭ xs)) v∈xs

sort-pres-↭ : ∀ {xs ys} → xs ↭ ys → sort xs ↭ sort ys
sort-pres-↭ {xs} {ys} xs↭ys = begin
  sort xs ↭⟨ sort↭ xs ⟩
  xs      ↭⟨ xs↭ys ⟩
  ys      ↭⟨ ↭-sym (sort↭ ys) ⟩
  sort ys ∎
  where open PermutationReasoning

↭⇒sort-≋ : ∀ {xs ys} → xs ↭ ys → sort xs ≋ sort ys
↭⇒sort-≋ {xs} {ys} xs↭ys = ↗↭↗⇒≋ (sort-pres-↭ xs↭ys) (sort↗ xs) (sort↗ ys)
