open import Data.List using (List; length)
open import Data.List.Membership.Setoid.Properties using (∈-length)
open import Function using (flip)
open import Data.Nat using (ℕ; _≤_)

open import RoutingLib.Data.List.Uniqueness.Setoid using (Unique)
open import RoutingLib.Data.List.Uniqueness.Setoid.Properties using (deduplicate!⁺)
open import RoutingLib.Data.List.Membership.DecSetoid.Properties using (∈-deduplicate⁺)

open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.Algebra.Properties.StrictlyIncreasingRoutingAlgebra
  as StrictlyIncreasingRoutingAlgebraProperties

module RoutingLib.Routing.Algebra.Properties.FiniteStrictlyIncreasingRoutingAlgebra
  {a b ℓ} (algebra : FiniteStrictlyIncreasingRoutingAlgebra a b ℓ) where

open FiniteStrictlyIncreasingRoutingAlgebra algebra
open import RoutingLib.Data.List.Sorting (flip _≤₊_) using (Sorted)

--------------------------------------------------------------------------------
-- Increasing path algebra

open StrictlyIncreasingRoutingAlgebraProperties strictlyIncreasingRoutingAlgebra public

open import RoutingLib.Data.List.Sorting.InsertionSort ≥₊-decTotalOrder
open import RoutingLib.Data.List.Membership.DecSetoid DS using (deduplicate)
open import Data.List.Membership.Setoid S using (_∈_)

abstract

  routes : List Route
  routes = sort (deduplicate allRoutes)

  routes! : Unique S routes
  routes! = sort!⁺ (deduplicate!⁺ DS allRoutes)

  ∈-routes : ∀ x → x ∈ routes
  ∈-routes x = ∈-sort⁺ (∈-deduplicate⁺ DS (∈-allRoutes x))

  routes↗ : Sorted routes
  routes↗ = sort↗ (deduplicate allRoutes)

H : ℕ
H = length routes

1≤H : 1 ≤ H
1≤H = ∈-length S (∈-routes ∞)
