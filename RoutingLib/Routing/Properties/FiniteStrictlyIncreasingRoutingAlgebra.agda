open import Data.List using (List; length)
open import Function using (flip)
open import Data.Nat using (ℕ; _≤_)

open import RoutingLib.Data.List.Uniqueness.Setoid using (Unique)
open import RoutingLib.Data.List.Uniqueness.Setoid.Properties using (deduplicate!⁺)
open import RoutingLib.Data.List.Membership.DecSetoid.Properties using (∈-deduplicate⁺)
open import RoutingLib.Data.List.Membership.Setoid.Properties using (∈-length)

open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.Properties.StrictlyIncreasingRoutingAlgebra
  as StrictlyIncreasingRoutingAlgebraProperties

module RoutingLib.Routing.Properties.FiniteStrictlyIncreasingRoutingAlgebra
  {a b ℓ} (algebra : FiniteStrictlyIncreasingRoutingAlgebra a b ℓ) where

open FiniteStrictlyIncreasingRoutingAlgebra algebra
open import RoutingLib.Data.List.Sorting (flip _≤₊_) using (Sorted)

--------------------------------------------------------------------------------
-- Increasing path algebra

open StrictlyIncreasingRoutingAlgebraProperties strictlyIncreasingRoutingAlgebra public

open import RoutingLib.Data.List.Sorting.Mergesort ≥₊-decTotalOrder
open import RoutingLib.Data.List.Membership.DecSetoid DS using (deduplicate)
open import Data.List.Any.Membership S using (_∈_)

abstract

  routes : List Route
  routes = mergesort (deduplicate allRoutes)

  routes! : Unique S routes
  routes! = mergesort!⁺ (deduplicate!⁺ DS allRoutes)

  ∈-routes : ∀ x → x ∈ routes
  ∈-routes x = ∈-mergesort⁺ (∈-deduplicate⁺ DS (∈-allRoutes x))

  routes↗ : Sorted routes
  routes↗ = mergesort↗ (deduplicate allRoutes)

H : ℕ
H = length routes

1≤H : 1 ≤ H
1≤H = ∈-length S (∈-routes ∞)
