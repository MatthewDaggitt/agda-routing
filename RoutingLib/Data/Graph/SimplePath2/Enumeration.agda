open import Data.Nat using (ℕ; _≤_; z≤n)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Any using (here; there)
open import Data.List.All using (_∷_)
open import Data.List.All.Properties using (All-universal)
open import Function using (_∘_; id)

open import RoutingLib.Data.List.All.Properties using (All-map⁺₂; AllPairs-map⁺₂)
open import RoutingLib.Data.List.All using (AllPairs; _∷_; [])
open import RoutingLib.Data.Graph.SimplePath2 hiding (_∈_)
open import RoutingLib.Data.Graph.SimplePath2.Properties using (ℙₛ)
open import RoutingLib.Data.Graph.SimplePath2.NonEmpty.Properties using () renaming (≈-setoid to NEPₛ)
open import RoutingLib.Data.List.Membership.Setoid.Properties using (∈-map⁺)
open import RoutingLib.Data.List.Uniqueness.Setoid using (Unique)

module RoutingLib.Data.Graph.SimplePath2.Enumeration where

  --import RoutingLib.Data.Graph.SimplePath2.NonEmpty.Enumeration as Eⁿᵗ

  private
    module _ {n : ℕ} where
      open import Data.List.Any.Membership (ℙₛ {n}) using (_∈_) public

  postulate allPaths : ∀ n → List (SimplePath n)
    {-
    allPaths n = ∅ ∷ [] ∷ map [_] (Eⁿᵗ.allPaths n)

    allPaths! : ∀ n → Unique ℙₛ (allPaths n)
    allPaths! n =
      ((λ()) ∷ All-map⁺₂ (λ _ ()) (Eⁿᵗ.allPaths n))
      ∷ All-map⁺₂ (λ _ ()) (Eⁿᵗ.allPaths n)
      ∷ AllPairs-map⁺₂ (_∘ [-]-injective ) (Eⁿᵗ.allPaths! n)
    -}
    
  postulate ∈-allPaths : ∀ {n} (p : SimplePath n) → p ∈ allPaths n
    {-
    ∈-allPaths {_} ∅     = here ∅
    ∈-allPaths {_} []    = there (here [])
    ∈-allPaths {n} [ x ] = there (there (∈-map⁺ NEPₛ ℙₛ [_] (Eⁿᵗ.∈-allPaths n x)))
    -}
