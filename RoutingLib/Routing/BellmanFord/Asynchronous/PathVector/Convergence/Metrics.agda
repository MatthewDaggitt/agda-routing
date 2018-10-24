open import Data.Fin using (Fin) renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Subset using (Subset; _∈_)
open import Data.Fin.Dec using (_∈?_)
open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties hiding (module ≤-Reasoning)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (if_then_else_)
open import Data.Product using (∃; _,_; proj₂)
open import Function using (_∘_)
open import Relation.Binary using (_Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import RoutingLib.Data.Table using (max)
open import RoutingLib.Data.Table.Properties using (max[t]<x; x≤max[t])
open import RoutingLib.Data.Nat.Properties using (module ≤-Reasoning; n≢0⇒0<n)
import RoutingLib.Function.Metric.Construct.Condition as Condition
import RoutingLib.Function.Metric.Construct.MaxLift as MaxLift
import RoutingLib.Function.Metric as Metric
import RoutingLib.Relation.Binary.Reasoning.PartialOrder as PO-Reasoning

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.CertifiedPathAlgebra
import RoutingLib.Routing.Algebra.RoutingAlgebra.Properties as RoutingAlgebraProperties
import RoutingLib.Routing.Model as Model
open import RoutingLib.Iteration.Asynchronous.Schedule using (Epoch)
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions

import RoutingLib.Routing.BellmanFord.Synchronous.PathVector.Properties as SyncBellmanFordProperties
import RoutingLib.Routing.BellmanFord.Asynchronous as AsyncBellmanFord
import RoutingLib.Routing.BellmanFord.Synchronous.PathVector.Convergence.Metrics as SyncMetrics
import RoutingLib.Routing.BellmanFord.Synchronous.PathVector.Convergence.Properties as SyncMetricProperties

module RoutingLib.Routing.BellmanFord.Asynchronous.PathVector.Convergence.Metrics
  {a b ℓ n} {algebra : RawRoutingAlgebra a b ℓ}
  (isPathAlgebra : IsCertifiedPathAlgebra algebra n)
  (A : Model.AdjacencyMatrix algebra n)
  (p : Subset n)
  
  where

open Model algebra n
open SyncMetrics isPathAlgebra A public using (dₜ) renaming (dᵣ to d)

dₜᶜ : ∀ (i : Fin n) → RoutingTable → RoutingTable → ℕ
dₜᶜ i x y = if ⌊ i ∈? p ⌋ then dₜ x y else 0

Dˢ : RoutingMatrix → RoutingMatrix → ℕ
Dˢ X Y = max 0 (λ i → dₜᶜ i (X i) (Y i))
