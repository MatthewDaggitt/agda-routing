open import Data.Nat using (ℕ; suc)
open import Data.Product using (∃; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.List using (List; length)

open import RoutingLib.Data.Matrix using (fold⁺)
open import RoutingLib.Data.List.Uniqueness.Setoid using (Unique)
open import RoutingLib.Data.List.Uniqueness.Setoid.Properties using (deduplicate!⁺)
open import RoutingLib.Data.List.Membership.DecSetoid.Properties using (∈-deduplicate⁺)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Routing.BellmanFord.DistanceVector.SufficientConditions

module RoutingLib.Routing.BellmanFord.DistanceVector.Prelude
  {a b ℓ n-1}
  {𝓡𝓐 : RoutingAlgebra a b ℓ}
  (𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1)) 
  (sc : SufficientConditions 𝓡𝓐)
  where

  open RoutingProblem 𝓡𝓟 public
  open SufficientConditions sc public

  open import RoutingLib.Routing.BellmanFord 𝓡𝓟 public
  open import RoutingLib.Routing.BellmanFord.Properties 𝓡𝓟 as P public using (Iᵢⱼ≡0#)
  open import Data.List.Any.Membership S using (_∈_)

  n : ℕ
  n = suc n-1
  
  -- A route is always either an extension of an existing route or the identity matrix
  σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ : ∀ X i j → (∃ λ k → σ X i j ≈ A i k ▷ X k j) ⊎ (σ X i j ≈ I i j)
  σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ = P.σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ ⊕-sel

  -- A▷ₘ always chooses the "best" option with respect to ⊕
  σXᵢⱼ≤Aᵢₖ▷Xₖⱼ : ∀ X i j k → σ X i j ≤ A i k ▷ X k j
  σXᵢⱼ≤Aᵢₖ▷Xₖⱼ = P.σXᵢⱼ≤Aᵢₖ▷Xₖⱼ ⊕-idem ⊕-assoc ⊕-comm

  -- After an iteration, the diagonal of the RMatrix is always the identity
  σXᵢᵢ≈Iᵢᵢ : ∀ X i → σ X i i ≈ I i i
  σXᵢᵢ≈Iᵢᵢ = P.σXᵢᵢ≈Iᵢᵢ ⊕-sel ⊕-assoc ⊕-comm 1#-anᵣ-⊕

  -- After an iteration, the diagonals of any two RMatrices are equal
  σXᵢᵢ≈σYᵢᵢ : ∀ X Y i → σ X i i ≈ σ Y i i
  σXᵢᵢ≈σYᵢᵢ = P.σXᵢᵢ≈σYᵢᵢ ⊕-sel ⊕-assoc ⊕-comm 1#-anᵣ-⊕


  -----------------------------
  -- A sorted list of routes --
  -----------------------------
  
  -- We have a unique complete list of routes

  open import RoutingLib.Data.List.Uniset DS using (Enumeration)
  open Enumeration routes-enumerable renaming (X to R-uniset; isEnumeration to R-isEnumeration)
  open import RoutingLib.Data.List.Sorting ≥-decTotalOrder using (Sorted)
  open import RoutingLib.Data.List.Sorting.Mergesort ≥-decTotalOrder using (mergesort; mergesort!⁺; ∈-mergesort⁺; mergesort↗)
  open import RoutingLib.Data.List.Membership.DecSetoid DS using (deduplicate)
  
  routes : List Route
  routes = mergesort (deduplicate (proj₁ R-uniset))

  routes! : Unique S routes
  routes! = mergesort!⁺ (deduplicate!⁺ DS (proj₁ R-uniset))

  ∈-routes : ∀ x → x ∈ routes
  ∈-routes x = ∈-mergesort⁺ (∈-deduplicate⁺ DS (R-isEnumeration x))

  routes↗ : Sorted routes
  routes↗ = mergesort↗ (deduplicate (proj₁ R-uniset))
 
  H : ℕ
  H = length routes
