open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Any using (here; there)
open import Function using (_∘_)

open import RoutingLib.Data.List.All.Properties using (All-map⁺₂; AllPairs-map⁺₂)
open import RoutingLib.Data.List.All using (_∷_; [])
open import RoutingLib.Data.Graph.SimplePath hiding (_∈_)
open import RoutingLib.Data.Graph.SimplePath.Properties using ([-]-injective; ℙₛ)
open import RoutingLib.Data.Graph.SimplePath.NonEmpty.Properties using () renaming (≈-setoid to NEPₛ)
open import RoutingLib.Data.List.Any.Membership.Properties using (∈-map⁺)
open import RoutingLib.Data.List.Uniqueness using (Unique)

module RoutingLib.Data.Graph.SimplePath.Enumeration where

  import RoutingLib.Data.Graph.SimplePath.NonEmpty.Enumeration as Eⁿᵗ

  private
    module _ {n : ℕ} where
      open import Data.List.Any.Membership (ℙₛ {n}) using (_∈_) public

  abstract
  
    allPaths : ∀ n → List (SimplePath n)
    allPaths n = [] ∷ map [_] (Eⁿᵗ.allPaths n)

    allPaths! : ∀ n → Unique ℙₛ (allPaths n)
    allPaths! n = All-map⁺₂ (λ _ ()) (Eⁿᵗ.allPaths n) ∷ AllPairs-map⁺₂ (_∘ [-]-injective ) (Eⁿᵗ.allPaths! n)

    ∈-allPaths : ∀ {n} (p : SimplePath n) → p ∈ allPaths n
    ∈-allPaths {_} []    = here []
    ∈-allPaths {n} [ x ] = there (∈-map⁺ NEPₛ ℙₛ [_] (Eⁿᵗ.∈-allPaths n x))
