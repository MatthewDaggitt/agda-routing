open import Data.Nat using (ℕ; suc; z≤n; s≤s; _∸_) renaming (_≤_ to _≤ℕ_; _≥_ to _≥ℕ_; _<_ to _<ℕ_)
open import Data.Nat.Properties using (<⇒≤; n∸m≤n) renaming (≤-reflexive to ≤ℕ-reflexive; ≤-trans to ≤ℕ-trans; ≤-antisym to ≤ℕ-antisym; ≤-decTotalOrder to ≤ℕ-decTotalOrder)
open import Data.List using (List; length)
open import Data.Product using (∃; _,_)
open import Relation.Binary using (_Preserves_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; module ≡-Reasoning)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.List using (index; between)
open import RoutingLib.Data.List.Uniqueness using (Unique)
open import RoutingLib.Data.List.Uniqueness.Properties using (between!⁺)
open import RoutingLib.Data.List.Sorting.Nat using (↗-between)
open import RoutingLib.Data.List.Any.Membership.Properties using (indexOf-cong; indexOf-revCong; indexOf-index; indexOf[xs]≤|xs|; indexOf[xs]<|xs|)
open import RoutingLib.Data.List.Any.Membership.Propositional using (∈-between⁺; ∈-between⁻)
open import RoutingLib.Data.Nat.Properties using (ℕₛ; ∸-cancelˡ-≡; ∸-monoˡ-<; ∸-cancelˡ-≤; m<n⇒0<n∸m; n∸1+m<n; m∸[m∸n]≡n)

open import RoutingLib.Routing.Definitions using (RoutingProblem; RoutingAlgebra)
open import RoutingLib.Routing.BellmanFord.DistanceVector.SufficientConditions using (SufficientConditions)
import RoutingLib.Routing.BellmanFord.DistanceVector.Prelude as Prelude

module RoutingLib.Routing.BellmanFord.DistanceVector.Step1_HeightFunction 
  {a b ℓ n-1}
  {𝓡𝓐 : RoutingAlgebra a b ℓ}
  (𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1)) 
  (𝓢𝓒 : SufficientConditions 𝓡𝓐)
  where
  
  open Prelude 𝓡𝓟 𝓢𝓒

  open import Data.List.Any.Membership ℕₛ using () renaming (_∈_ to _∈ℕ_)

  open import RoutingLib.Data.List.Any.Membership S using (indexOf)
  open import RoutingLib.Data.List.Sorting.Properties ≤-decTotalOrder using (↗-indexOf-mono-<)


  abstract
  
    -- The height of an element x is h(x) = H ∸ |{y | y ≤ x}|

    
    h : Route → ℕ
    h x = H ∸ indexOf (∈-↗routes x)

    h-resp-≈ : ∀ {u v} → u ≈ v → h u ≡ h v
    h-resp-≈ {u} {v} u≈v = cong (H ∸_) (indexOf-cong S u≈v (∈-↗routes u) (∈-↗routes v) ↗routes!)
    
    h-resp-< : ∀ {u v} → u < v → h v <ℕ h u
    h-resp-< {u} {v} u<v = ∸-monoˡ-< (↗-indexOf-mono-< ↗-↗routes (∈-↗routes u) (∈-↗routes v) u<v) (indexOf[xs]≤|xs| S _)

    1≤h : ∀ x → 1 ≤ℕ h x
    1≤h x = m<n⇒0<n∸m (indexOf[xs]<|xs| S (∈-↗routes x)) --s≤s z≤n

{-
    h≤H : ∀ x → h x ≤ℕ H
    h≤H x = n∸m≤n (indexOf (∈-↗routes x)) H

    1≤H : 1 ≤ℕ H
    1≤H = ≤ℕ-trans (1≤h 0#) (h≤H 0#)
-}
