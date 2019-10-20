
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing as Routing using (AdjacencyMatrix)

module RoutingLib.Routing.VectorBased.Asynchronous.PathVector.Convergence.RouteDistanceFunction
  {a b ℓ n} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (isPathAlgebra : IsCertifiedPathAlgebra algebra n)
  (A : AdjacencyMatrix algebra n)
  where

open import Data.Fin using (Fin) renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Subset using (Subset; _∈_)
open import Data.Fin.Dec using (_∈?_)
open import Data.Nat hiding (_≟_)
open import Data.Bool using (if_then_else_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import RoutingLib.Data.Table using (max; zipWith)

import RoutingLib.Routing.Algebra.Properties.FiniteRoutingAlgebra as FiniteRoutingAlgebraProperties
import RoutingLib.Routing.Algebra.Construct.Consistent as Consistent

open Routing algebra n
open RawRoutingAlgebra algebra
open IsCertifiedPathAlgebra isPathAlgebra
open Consistent isRoutingAlgebra isPathAlgebra A
open FiniteRoutingAlgebraProperties isRoutingAlgebraᶜ isFiniteᶜ using (H)

module DV = DistanceVectorMetrics isRoutingAlgebraᶜ isFiniteᶜ

-- Height of inconsistent routes
hⁱ : Route → ℕ
hⁱ x with 𝑪? x
... | yes _ = 1
... | no  _ = suc n ∸ size x

-- Distance between inconsistent routes
rⁱ : Route → Route → ℕ
rⁱ x y = hⁱ x ⊔ hⁱ y

-- Distance between consistent routes
rᶜ : ∀ {x y} → 𝑪 x → 𝑪 y → ℕ
rᶜ xᶜ yᶜ = DV.r (toCRoute xᶜ) (toCRoute yᶜ)

-- Distance between routes
r : Route → Route → ℕ
r x y with x ≟ y | 𝑪? x | 𝑪? y
... | yes _ | _      | _      = zero
... | no  _ | yes xᶜ | yes yᶜ = rᶜ xᶜ yᶜ
... | no  _ | _      | _      = suc H + rⁱ x y

-- Distance between routing tables
d : RoutingTable → RoutingTable → ℕ
d x y = max 0 (zipWith r x y)

-- Conditional distance between routing tables
dᶜ : Subset n → Fin n → RoutingTable → RoutingTable → ℕ
dᶜ p i x y = if ⌊ i ∈? p ⌋ then d x y else 0

-- Distance between routing states
D : Subset n → RoutingMatrix → RoutingMatrix → ℕ
D p X Y = max 0 (λ i → dᶜ p i (X i) (Y i))
