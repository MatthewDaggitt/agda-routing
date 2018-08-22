open import Data.Nat using (ℕ; _≤_; _<_; z≤n)
open import Data.List using (List; _∷_; map)
open import Data.List.Any using (here; there)
open import Data.List.All using (_∷_)
open import Data.List.Membership.Setoid.Properties using (∈-map⁺)

open import RoutingLib.Data.Path.EdgePath hiding (_∈_)
open import RoutingLib.Data.Path.EdgePath.Relation.Equality
open import RoutingLib.Data.Path.EdgePath.NonEmpty.Relation.Equality
  using () renaming (ℙₛ to NEℙₛ)
open import RoutingLib.Data.Path.EdgePath.All using (Allₙ; valid)

module RoutingLib.Data.Path.EdgePath.Enumeration where

  import RoutingLib.Data.Path.EdgePath.NonEmpty.Enumeration as Eⁿᵗ
  open import Data.List.Membership.Setoid ℙₛ using (_∈_) public

  abstract
  
    allPaths : ℕ → List Path
    allPaths n = invalid ∷ map valid (Eⁿᵗ.allPaths n)

    ∈-allPaths : ∀ {p n} → Allₙ (_< n) p → p ∈ allPaths n
    ∈-allPaths {invalid} {_} _           = here invalid
    ∈-allPaths {valid p} {n} (valid p<n) = there (∈-map⁺ NEℙₛ ℙₛ valid (Eⁿᵗ.∈-allPaths n p<n))
