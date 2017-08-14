open import Data.Nat using (ℕ; _<_) renaming (decTotalOrder to ≤-decTotalOrder)
open import Data.List.All using () renaming (map to mapₐ)
open import Data.Product using (uncurry′)
open import Relation.Binary using (DecTotalOrder)
open import Relation.Binary.PropositionalEquality using () renaming (setoid to ≡-setoid)

open import RoutingLib.Data.List.All using (AllPairs; []; _∷_) using (allPairs-product; allPairs-map)
open import RoutingLib.Data.List.Sorting
open import RoutingLib.Data.List.Uniqueness using (Unique)
open import RoutingLib.Data.Nat.Properties using (≤+≢⇒<)

module RoutingLib.Data.List.Sorting.Nat where

  strictlySorted : ∀ {xs} → Sorted ≤-decTotalOrder xs → Unique (≡-setoid ℕ) xs → AllPairs _<_ xs
  strictlySorted xs↑ xs! = allPairs-map (uncurry′ ≤+≢⇒<) (allPairs-product xs↑ xs!)
