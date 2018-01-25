open import Data.Nat using (ℕ; pred; suc; z≤n; s≤s; _∸_) renaming (_≤_ to _≤ℕ_; _≥_ to _≥ℕ_; _<_ to _<ℕ_)
open import Data.Nat.Properties using (<⇒≤; n∸m≤n) renaming (≤-reflexive to ≤ℕ-reflexive; ≤-trans to ≤ℕ-trans; ≤-antisym to ≤ℕ-antisym; ≤-decTotalOrder to ≤ℕ-decTotalOrder)
open import Data.Fin using (toℕ)
open import Data.Fin.Properties using (prop-toℕ-≤)
open import Data.List using (List; length)
open import Data.List.Any using (index)
open import Data.Product using (∃; _,_)
open import Relation.Binary using (_Preserves_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; subst; module ≡-Reasoning)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_)

open import RoutingLib.Data.Fin.Properties using (toℕ-mono-<)
open import RoutingLib.Data.List using (between)
open import RoutingLib.Data.List.Uniqueness.Setoid using (Unique)
open import RoutingLib.Data.List.Membership.Setoid.Properties using (index-cong; ∈-length)
open import RoutingLib.Data.List.Membership.Setoid.Properties using ()
open import RoutingLib.Data.Nat.Properties using (ℕₛ; ∸-cancelˡ-≡; ∸-cancelʳ-≤; m<n⇒0<n∸m; n∸1+m<n; m∸[m∸n]≡n; suc∘pred[n]≡n)

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

  open import RoutingLib.Data.List.Membership.Setoid S using ()
  open import RoutingLib.Data.List.Sorting.Properties ≥-decTotalOrder using (index-mono-<)


  abstract
  
    -- The height of an element x is h(x) = |{y | x ≤ y}|

    h : Route → ℕ
    h x = suc (toℕ (index (∈-routes x)))
    
    h-resp-≈ : ∀ {u v} → u ≈ v → h u ≡ h v
    h-resp-≈ u≈v = cong (suc ∘ toℕ) (index-cong S u≈v (∈-routes _) (∈-routes _) routes!)
    
    h-resp-< : ∀ {u v} → u < v → h v <ℕ h u
    h-resp-< (u≤v , u≉v) = s≤s (toℕ-mono-< (index-mono-< routes↗ (∈-routes _) (∈-routes _) (u≤v , u≉v ∘ ≈-sym)))
      
    1≤h : ∀ x → 1 ≤ℕ h x
    1≤h x = s≤s z≤n

    h≤H : ∀ x → h x ≤ℕ H
    h≤H x = subst (h x ≤ℕ_) (suc∘pred[n]≡n 1≤H) (s≤s (prop-toℕ-≤ (index (∈-routes x))))
      
    
