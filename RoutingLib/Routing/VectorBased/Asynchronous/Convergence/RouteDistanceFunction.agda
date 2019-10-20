open import RoutingLib.Routing using (AdjacencyMatrix)
open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.VectorBased.Asynchronous.Convergence.RouteDistanceFunction
  {a b ℓ} {alg : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra alg)
  {n} (A : AdjacencyMatrix alg n)
  where

open RawRoutingAlgebra alg
open IsRoutingAlgebra isRoutingAlgebra

open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties hiding (_≟_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Level using () renaming (_⊔_ to _⊔ₗ_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.PartialOrder as POR

open import RoutingLib.Data.Nat.Properties

open import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra isRoutingAlgebra
open import RoutingLib.Routing.VectorBased.Synchronous alg A
open import RoutingLib.Routing.VectorBased.Synchronous.DistanceVector.Properties isRoutingAlgebra A
open import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.HeightFunction alg A
open import RoutingLib.Function.Metric.Nat 

------------------------------------------------------------------------
-- Definition

record RouteDistanceFunction : Set (a ⊔ₗ ℓ) where
  field
    r                   : Route → Route → ℕ
    r-isQuasiSemiMetric : IsQuasiSemiMetric _≈_ r 
    r-bounded           : Bounded r
    r-strContrOrbits    : ∀ {X v} → 0 < v → (∀ k l → r (X k l) (F X k l) ≤ v) →
                          ∀ i j → r (F X i j) (F (F X) i j) < v
    r-strContrFP        : ∀ {X*} → F X* ≈ₘ X* →
                          ∀ {X v} → 0 < v → (∀ k l → r (X* k l) (X k l) ≤ v) →
                          ∀ i j → r (X* i j) (F X i j) < v

  open IsQuasiSemiMetric r-isQuasiSemiMetric public
