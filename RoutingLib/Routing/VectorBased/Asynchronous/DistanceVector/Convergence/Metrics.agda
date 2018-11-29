open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Subset using (Subset)
open import Data.Fin.Dec using (_∈?_)
open import Data.List using (length)
open import Data.List.Any using (index)
open import Data.Nat using (ℕ; zero; suc; _⊔_)
open import Data.Bool using (if_then_else_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import RoutingLib.Data.Table using (max; zipWith)

import RoutingLib.Routing as Routing
open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.Algebra.Properties.FiniteRoutingAlgebra as FiniteRoutingAlgebraProperties

module RoutingLib.Routing.VectorBased.Asynchronous.DistanceVector.Convergence.Metrics
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (isFinite : IsFinite algebra)
  where

open Routing algebra
open RawRoutingAlgebra algebra
open FiniteRoutingAlgebraProperties isRoutingAlgebra isFinite

-- Some notational shorthand for the index of route u in the list of routes
i[_] : Route → Fin (length routes)
i[ u ] = index (∈-routes u)

-- The height of an element x is the number of
-- elements above it in the order (i.e. |{y | x ≤ y}|)
h : Route → ℕ
h x = suc (toℕ (i[ x ]))

-- The distance between two routes
r : Route → Route → ℕ
r x y with x ≟ y
... | yes _ = zero
... | no  _ = h x ⊔ h y

-- The distance between two routing tables
d : ∀ {n} → RoutingTable n → RoutingTable n → ℕ
d x y = max 0 (zipWith r x y)

-- The conditional distance between two routing tables
dᶜ : ∀ {n} (p : Subset n) → (i : Fin n) → RoutingTable n → RoutingTable n → ℕ
dᶜ p i x y = if ⌊ i ∈? p ⌋ then d x y else 0

-- The distance between two routing states
D : ∀ {n} (p : Subset n) → RoutingMatrix n → RoutingMatrix n → ℕ
D p X Y = max 0 (λ i → dᶜ p i (X i) (Y i))
