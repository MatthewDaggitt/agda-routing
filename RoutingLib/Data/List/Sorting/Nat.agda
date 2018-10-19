open import Data.Nat using (ℕ; _<_; _≤_; _≥_; z≤n; s≤s)
open import Data.Nat.Properties using (≤+≢⇒<; <⇒≯; <⇒≤; ≤-decTotalOrder; n≮n)
open import Data.Fin using (zero; suc) renaming (_<_ to _<𝔽_)
open import Data.List using (upTo; downFrom; lookup)
open import Data.List.All using () renaming (map to mapₐ; lookup to lookupₐ)
open import Data.List.Membership.Propositional.Properties using (∈-lookup)
open import Data.Product using (_,_; uncurry′)
open import Relation.Binary using (DecTotalOrder)
open import Relation.Binary.PropositionalEquality using () renaming (setoid to ≡-setoid)
open import Function using (id)
open import Relation.Nullary.Negation using (contradiction)

import RoutingLib.Data.List.Sorting as Sorting
open import RoutingLib.Data.List
open import RoutingLib.Data.List.Uniqueness.Propositional using (Unique)
open import RoutingLib.Data.List.AllPairs using (AllPairs; []; _∷_; map; zip)
open import RoutingLib.Data.List.AllPairs.Properties using (applyUpTo⁺₁)

module RoutingLib.Data.List.Sorting.Nat where

  open Sorting _≤_ using () renaming (Sorted to ↑-Sorted)
  open Sorting _≥_ using () renaming (Sorted to ↓-Sorted)

  strictlySorted : ∀ {xs} → ↑-Sorted xs → Unique xs → AllPairs _<_ xs
  strictlySorted xs↑ xs! = map (uncurry′ ≤+≢⇒<) (zip (xs↑ , xs!))

  upTo-↗ : ∀ e → ↑-Sorted (upTo e)
  upTo-↗ e = applyUpTo⁺₁ e (λ i<j _ → <⇒≤ i<j)

  postulate downFrom-↘ : ∀ e → ↓-Sorted (downFrom e) 
  {-
  between-↗ : ∀ e s → Sorted (between e s)
  between-↗ e s = AllPairs-applyBetween⁺₁ id e s (λ _ i<j _ → <⇒≤ i<j)
  -}

  index-mono⁻¹-< : ∀ {xs} → ↑-Sorted xs → Unique xs → ∀ {i j} → lookup xs i < lookup xs j → i <𝔽 j
  index-mono⁻¹-< [] []                     {()}
  index-mono⁻¹-< (x≤xs ∷ xs↗) (x≉xs ∷ xs!) {zero}  {zero}  x<x     = contradiction x<x (n≮n _)
  index-mono⁻¹-< (x≤xs ∷ xs↗) (x≉xs ∷ xs!) {zero}  {suc j} x<xsⱼ   = s≤s z≤n
  index-mono⁻¹-< (x≤xs ∷ xs↗) (x≉xs ∷ xs!) {suc i} {zero}  xsᵢ<x   = contradiction (≤+≢⇒< (lookupₐ x≤xs (∈-lookup _ i)) (lookupₐ x≉xs (∈-lookup _ i))) (<⇒≯ xsᵢ<x)
  index-mono⁻¹-< (x≤xs ∷ xs↗) (x≉xs ∷ xs!) {suc i} {suc j} xsᵢ<xsⱼ = s≤s (index-mono⁻¹-< xs↗ xs! xsᵢ<xsⱼ)

  postulate index-mono⁻¹-> : ∀ {xs} → ↓-Sorted xs → Unique xs → ∀ {i j} → lookup xs i < lookup xs j → j <𝔽 i
