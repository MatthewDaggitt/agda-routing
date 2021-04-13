open import Data.List
open import Data.List.Relation.Unary.All using ([]; _∷_; map)
import Data.List.Relation.Unary.Unique.Setoid as Uniqueness
import Data.List.Membership.Setoid as Membership
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (↭-empty-inv)
open import Relation.Binary using (TotalOrder; _Preserves_⟶_; _Respects_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Unary using (Pred; Decidable)

import Data.List.Relation.Unary.Sorted.TotalOrder as Sorted
open import Data.List.Relation.Unary.Sorted.TotalOrder.Properties using (filter⁺)

open import Data.List.Sort.Base
open import RoutingLib.Data.List.Relation.Unary.All.Properties as All
open import RoutingLib.Data.List.Relation.Binary.Permutation.Propositional.Properties

module RoutingLib.Data.List.Sort.Properties
  {a ℓ₁ ℓ₂} {totalOrder : TotalOrder a ℓ₁ ℓ₂}
  (sortingAlgorithm : SortingAlgorithm totalOrder) where

open TotalOrder totalOrder renaming (Carrier to A)

open import Data.List.Relation.Binary.Permutation.Setoid Eq.setoid
open import Data.List.Relation.Binary.Permutation.Setoid.Properties Eq.setoid as Perm
  using (Unique-resp-↭; ∈-resp-↭)
open import Data.List.Relation.Binary.Equality.Setoid Eq.setoid using (_≋_)

import RoutingLib.Data.List.Relation.Unary.Sorted.Properties totalOrder as Sortedₚ

open SortingAlgorithm sortingAlgorithm

open Sorted totalOrder
open Uniqueness Eq.setoid using (Unique)
open Membership Eq.setoid using (_∈_)

sort-[] : sort [] ≡ []
sort-[] = ↭-empty-inv (sort-↭ [])

sort-↭ₛ : ∀ xs → sort xs ↭ xs
sort-↭ₛ xs = toSetoid Eq.setoid (sort-↭ xs)

sort!⁺ : ∀ {xs} → Unique xs → Unique (sort xs)
sort!⁺ {xs} xs! = Unique-resp-↭ (↭-sym (sort-↭ₛ xs)) xs!

∈-sort⁺ : ∀ {v xs} → v ∈ xs → v ∈ sort xs
∈-sort⁺ {_} {xs} v∈xs = ∈-resp-↭ (↭-sym (sort-↭ₛ xs)) v∈xs

sort-pres-↭ : ∀ {xs ys} → xs ↭ ys → sort xs ↭ sort ys
sort-pres-↭ {xs} {ys} xs↭ys = begin
  sort xs ↭⟨  sort-↭ₛ xs ⟩
  xs      ↭⟨  xs↭ys ⟩
  ys      ↭˘⟨ sort-↭ₛ ys ⟩
  sort ys ∎
  where open PermutationReasoning

↭⇒sort-≋ : ∀ {xs ys} → xs ↭ ys → sort xs ≋ sort ys
↭⇒sort-≋ xs↭ys = Sortedₚ.↗↭↗⇒≋ (sort-↗ _) (sort-↗ _) (sort-pres-↭ xs↭ys)

sort-commutes-≋ : ∀ {f : List A → List A} →
                f Preserves _↭_ ⟶ _↭_ →
                (∀ {xs} → Sorted xs → Sorted (f xs)) →
                ∀ xs → sort (f xs) ≋ f (sort xs)
sort-commutes-≋ {f = f} pres-↭ pres-↗ xs = Sortedₚ.↗↭↗⇒≋ (sort-↗ (f xs)) (pres-↗ (sort-↗ xs)) (begin
  sort (f xs) ↭⟨  sort-↭ₛ (f xs) ⟩
  f xs        ↭˘⟨ pres-↭ (sort-↭ₛ xs) ⟩
  f (sort xs) ∎)
  where open PermutationReasoning

sort-filter-≋ : ∀ {p} {P : Pred A p} (P? : Decidable P) → P Respects _≈_ →
              ∀ xs → sort (filter P? xs) ≋ filter P? (sort xs)
sort-filter-≋ P? resp = sort-commutes-≋ (Perm.filter⁺ P? resp) (filter⁺ totalOrder P?)
