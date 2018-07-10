open import Data.Nat using (ℕ; _≤_; z≤n)
open import Data.List using (List; _∷_; map)
open import Data.List.Any using (here; there)
open import Data.List.All using (_∷_)
open import Data.List.Membership.Setoid.Properties using (∈-map⁺)

open import RoutingLib.Data.SimplePath hiding (_∈_)
open import RoutingLib.Data.SimplePath.Relation.Equality
open import RoutingLib.Data.SimplePath.NonEmpty.Relation.Equality
  using () renaming (ℙₛ to NEℙₛ)

module RoutingLib.Data.SimplePath.Enumeration where

  import RoutingLib.Data.SimplePath.NonEmpty.Enumeration as Eⁿᵗ

  private
    module _ {n : ℕ} where
      open import Data.List.Membership.Setoid (ℙₛ n) using (_∈_) public

  allPaths : ∀ n → List (SimplePath n)
  allPaths n = invalid ∷ map valid (Eⁿᵗ.allPaths n)

  ∈-allPaths : ∀ {n} (p : SimplePath n) → p ∈ allPaths n
  ∈-allPaths {_} invalid   = here invalid
  ∈-allPaths {n} (valid p) = there (∈-map⁺ (NEℙₛ n) (ℙₛ n) valid (Eⁿᵗ.∈-allPaths n p))
