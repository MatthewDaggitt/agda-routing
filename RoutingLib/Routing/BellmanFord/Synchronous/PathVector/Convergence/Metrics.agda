open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _≤_)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Data.Table using (max; zipWith)

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.CertifiedPathAlgebra
import RoutingLib.Routing.Algebra.CertifiedPathAlgebra.Consistency as Consistency
open import RoutingLib.Routing.Model as Model using (AdjacencyMatrix)
import RoutingLib.Routing.BellmanFord.Synchronous.DistanceVector.Convergence.Metrics as DistanceVectorMetrics

module RoutingLib.Routing.BellmanFord.Synchronous.PathVector.Convergence.Metrics
  {a b ℓ n} {algebra : RawRoutingAlgebra a b ℓ}
  (isPathAlgebra : IsCertifiedPathAlgebra algebra n)
  (A : Model.AdjacencyMatrix algebra n)
  where

open Model algebra n
open RawRoutingAlgebra algebra
open IsCertifiedPathAlgebra isPathAlgebra
open Consistency algebra isPathAlgebra A

module DV = DistanceVectorMetrics isRoutingAlgebraᶜ isFiniteᶜ

-- Height of inconsistent routes
hⁱ : Route → ℕ
hⁱ r with 𝑪? r
... | yes _ = 1
... | no  _ = suc n ∸ size r

-- Distance between inconsistent routes
dᵣⁱ : Route → Route → ℕ
dᵣⁱ x y = hⁱ x ⊔ hⁱ y

-- Distance between consistent routes
dᵣᶜ : ∀ {x y} → 𝑪 x → 𝑪 y → ℕ
dᵣᶜ xᶜ yᶜ = DV.d (toCRoute xᶜ) (toCRoute yᶜ)

Hᶜ : ℕ
Hᶜ = suc DV.H

-- Distance between routes
dᵣ : Route → Route → ℕ
dᵣ x y with x ≟ y | 𝑪? x | 𝑪? y
... | yes _ | _      | _      = zero
... | no  _ | yes xᶜ | yes yᶜ = dᵣᶜ xᶜ yᶜ
... | no  _ | _      | _      = Hᶜ + dᵣⁱ x y

-- Distance between routing tables
dₜ : RoutingTable → RoutingTable → ℕ
dₜ x y = max 0 (zipWith dᵣ x y)

-- Distance between routing matrices
D : RoutingMatrix → RoutingMatrix → ℕ
D X Y = max 0 (zipWith dₜ X Y)
