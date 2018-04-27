open import Data.Nat using (ℕ; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤+≢⇒<; <⇒≯; <⇒≤; ≤-decTotalOrder; n≮n)
open import Data.Fin using (zero; suc) renaming (_<_ to _<𝔽_)
open import Data.List
open import Data.List.All using () renaming (map to mapₐ; lookup to lookupₐ)
open import Data.Product using (uncurry′)
open import Relation.Binary using (DecTotalOrder)
open import Relation.Binary.PropositionalEquality using () renaming (setoid to ≡-setoid)
open import Function using (id)
open import Relation.Nullary.Negation using (contradiction)

import RoutingLib.Data.List.Sorting as Sorting
open import RoutingLib.Data.List
open import RoutingLib.Data.List.Uniqueness.Propositional using (Unique)
open import RoutingLib.Data.List.All using (AllPairs; []; _∷_) using (allPairs-product; allPairs-map)
open import RoutingLib.Data.List.All.Properties using (AllPairs-applyUpTo⁺₁)
open import RoutingLib.Data.List.Membership.Propositional.Properties using (∈-lookup)

module RoutingLib.Data.List.Sorting.Nat where

  open Sorting ≤-decTotalOrder using (Sorted)
  
  strictlySorted : ∀ {xs} → Sorted xs → Unique xs → AllPairs _<_ xs
  strictlySorted xs↑ xs! = allPairs-map (uncurry′ ≤+≢⇒<) (allPairs-product xs↑ xs!)

  upTo-↗ : ∀ e → Sorted (upTo e) 
  upTo-↗ e = AllPairs-applyUpTo⁺₁ id e (λ i<j _ → <⇒≤ i<j)

  {-
  between-↗ : ∀ e s → Sorted (between e s)
  between-↗ e s = AllPairs-applyBetween⁺₁ id e s (λ _ i<j _ → <⇒≤ i<j)
  -}
  
  index-mono⁻¹-< : ∀ {xs} → Sorted xs → Unique xs → ∀ {i j} → lookup xs i < lookup xs j → i <𝔽 j
  index-mono⁻¹-< [] []                     {()}
  index-mono⁻¹-< (x≤xs ∷ xs↗) (x≉xs ∷ xs!) {zero}  {zero}  x<x     = contradiction x<x (n≮n _)
  index-mono⁻¹-< (x≤xs ∷ xs↗) (x≉xs ∷ xs!) {zero}  {suc j} x<xsⱼ   = s≤s z≤n
  index-mono⁻¹-< (x≤xs ∷ xs↗) (x≉xs ∷ xs!) {suc i} {zero}  xsᵢ<x   = contradiction (≤+≢⇒< (lookupₐ x≤xs (∈-lookup _ i)) (lookupₐ x≉xs (∈-lookup _ i))) (<⇒≯ xsᵢ<x)
  index-mono⁻¹-< (x≤xs ∷ xs↗) (x≉xs ∷ xs!) {suc i} {suc j} xsᵢ<xsⱼ = s≤s (index-mono⁻¹-< xs↗ xs! xsᵢ<xsⱼ)
