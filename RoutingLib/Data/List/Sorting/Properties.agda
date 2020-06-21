open import Relation.Binary
open import RoutingLib.Data.List.Sorting.Core

module RoutingLib.Data.List.Sorting.Properties
  {a ℓ₁ ℓ₂} (totalOrder : TotalOrder a ℓ₁ ℓ₂)
  (sortingAlgorithm : SortingAlgorithm totalOrder) where

open TotalOrder totalOrder renaming (Carrier to A)

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

import RoutingLib.Data.List.Relation.Unary.Sorted as Sorted
import RoutingLib.Data.List.Relation.Unary.Sorted.Properties as Sortedₚ

open SortingAlgorithm sortingAlgorithm

open Sorted totalOrder
-- open Sortedₚ totalOrder
open Uniqueness Eq.setoid using (Unique)
open Membership Eq.setoid using (_∈_)

sort!⁺ : ∀ {xs} → Unique xs → Unique (sort xs)
sort!⁺ {xs} xs! = Unique-resp-↭ (↭-sym (sort-↭ xs)) xs!

∈-sort⁺ : ∀ {v xs} → v ∈ xs → v ∈ sort xs
∈-sort⁺ {_} {xs} v∈xs = ∈-resp-↭ (↭-sym (sort-↭ xs)) v∈xs

sort-pres-↭ : ∀ {xs ys} → xs ↭ ys → sort xs ↭ sort ys
sort-pres-↭ {xs} {ys} xs↭ys = begin
  sort xs ↭⟨ sort-↭ xs ⟩
  xs      ↭⟨ xs↭ys ⟩
  ys      ↭⟨ ↭-sym (sort-↭ ys) ⟩
  sort ys ∎
  where open PermutationReasoning

↭⇒sort-≋ : ∀ {xs ys} → xs ↭ ys → sort xs ≋ sort ys
↭⇒sort-≋ {xs} {ys} xs↭ys = ↗↭↗⇒≋ (sort-pres-↭ xs↭ys) (sort-↗ xs) (sort-↗ ys)
