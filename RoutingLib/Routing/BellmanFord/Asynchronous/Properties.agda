open import Data.Fin.Subset using (Subset; ∣_∣)
open import Data.Fin.Dec using (_∈?_)
open import Data.Nat using (ℕ; _≤_)
open import Data.Bool using (if_then_else_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import RoutingLib.Data.Table using (max)

open import RoutingLib.Iteration.Asynchronous.Schedule using (Epoch)
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.CertifiedPathAlgebra

import RoutingLib.Routing.BellmanFord.Asynchronous as AsynchronousBellmanFord
import RoutingLib.Routing.BellmanFord.Synchronous as SynchronousBellmanFord
import RoutingLib.Routing.BellmanFord.Synchronous.PathVector.Convergence.Metrics as PathVectorMetrics
import RoutingLib.Routing.Model as Model


module RoutingLib.Routing.BellmanFord.Asynchronous.Properties
  {a b ℓ n} (algebra : RawRoutingAlgebra a b ℓ)
  (isPathAlgebra : IsCertifiedPathAlgebra algebra n)
  (isStrictlyIncreasing : IsStrictlyIncreasing algebra)
  (network : Epoch → Model.AdjacencyMatrix algebra n)
  (1≤n : 1 ≤ n)
  where

open Model algebra n
open PathVectorMetrics isPathAlgebra {!!} --isStrictlyIncreasing

dₛᵢ : Subset n → ∀ {i} → RoutingTable → RoutingTable → ℕ
dₛᵢ p {i} x y = if ⌊ i ∈? p ⌋ then dₜ x y else 0
  
d : Subset n → RoutingMatrix → RoutingMatrix → ℕ
d p x y = max 0 (λ i → dₛᵢ p (x i) (y i))
