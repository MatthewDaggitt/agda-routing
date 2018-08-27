open import Data.Nat using (ℕ; _≤_; z≤n)
open import Data.List using (List; _∷_; map)
open import Data.List.Any using (here; there)
open import Data.List.All using (_∷_)
open import Data.List.Membership.Setoid.Properties using (∈-map⁺)

open import RoutingLib.Data.Path.CertifiedI
open import RoutingLib.Data.Path.CertifiedI.Properties

module RoutingLib.Data.Path.CertifiedI.Enumeration where

  import RoutingLib.Data.Path.Certified.Enumeration as Eⁿᵗ

  private
    module _ {n : ℕ} where
      open import Data.List.Membership.Setoid (ℙₛ n) using (_∈_) public

  allPaths : ∀ n → List (Path n)
  allPaths n = invalid ∷ map valid (Eⁿᵗ.allPaths n)

  ∈-allPaths : ∀ {n} (p : Path n) → p ∈ allPaths n
  ∈-allPaths {_} invalid   = here invalid
  ∈-allPaths {n} (valid p) = there (∈-map⁺ (ℙᵛₛ n) (ℙₛ n) valid (Eⁿᵗ.∈-allPaths n p))
