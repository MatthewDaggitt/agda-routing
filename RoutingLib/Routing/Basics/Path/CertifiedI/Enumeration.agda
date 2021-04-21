open import Data.Nat using (ℕ; _≤_; z≤n)
open import Data.List using (List; _∷_; map)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.List.Membership.Setoid.Properties using (∈-map⁺)

module RoutingLib.Routing.Basics.Path.CertifiedI.Enumeration where

open import RoutingLib.Relation.Nullary.Finite.List.Setoid
  renaming (Finite to ListFinite)
open import RoutingLib.Relation.Nullary.Finite.List.Setoid.Properties
open import RoutingLib.Relation.Nullary.Finite.Bijection.Setoid
  using (Finite)

open import RoutingLib.Routing.Basics.Path.CertifiedI
open import RoutingLib.Routing.Basics.Path.CertifiedI.Properties
import RoutingLib.Routing.Basics.Path.Certified.Enumeration as Eⁿᵗ

private
  module _ {n : ℕ} where
    open import Data.List.Membership.Setoid (ℙₛ n) using (_∈_) public

allPaths : ∀ n → List (Path n)
allPaths n = invalid ∷ map valid (Eⁿᵗ.allPaths n)

allPaths-complete : ∀ {n} (p : Path n) → p ∈ allPaths n
allPaths-complete {_} invalid   = here invalid
allPaths-complete {n} (valid p) = there (∈-map⁺ (ℙᵛₛ n) (ℙₛ n) valid (Eⁿᵗ.∈-allPaths n p))

finiteₗ : ∀ n → ListFinite (ℙₛ n)
finiteₗ n = complete? (ℙₛ? n) allPaths-complete

finite : ∀ n → Finite (ℙₛ n)
finite n = Finite⇒Finiteₛ (finiteₗ n)
