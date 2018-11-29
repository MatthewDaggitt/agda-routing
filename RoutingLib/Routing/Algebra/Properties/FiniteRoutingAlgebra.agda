open import Data.List using (List; length)
open import Data.List.Membership.Setoid.Properties using (∈-length)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (proj₁; proj₂)
open import Function using (flip)

open import RoutingLib.Data.List.Uniqueness.Setoid using (Unique)
open import RoutingLib.Data.List.Uniqueness.Setoid.Properties using (deduplicate!⁺)
open import RoutingLib.Data.List.Membership.DecSetoid.Properties using (∈-deduplicate⁺)

open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra as RoutingAlgebraProperties

module RoutingLib.Routing.Algebra.Properties.FiniteRoutingAlgebra
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (isFinite : IsFinite algebra)
  where

open RawRoutingAlgebra algebra
open RoutingAlgebraProperties isRoutingAlgebra public

open import RoutingLib.Data.List.Sorting (flip _≤₊_) using (Sorted)

open import RoutingLib.Data.List.Sorting.InsertionSort ≥₊-decTotalOrder
open import RoutingLib.Data.List.Membership.DecSetoid DS using (deduplicate)
open import Data.List.Membership.Setoid S using (_∈_)

private

  allRoutes : List Route
  allRoutes = proj₁ isFinite

  ∈-allRoutes : ∀ r → r ∈ allRoutes
  ∈-allRoutes = proj₂ isFinite

abstract

  routes : List Route
  routes = sort (deduplicate (proj₁ isFinite))

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
