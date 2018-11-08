open import Data.Nat using (zero; suc; s≤s; z≤n)

import RoutingLib.Routing.Model as Model
open import RoutingLib.Routing.Algebra
open import RoutingLib.Iteration.Asynchronous.Dynamic using (Convergent)
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Theorems
  using (UltrametricConditions; ultra⇒convergent; |0|-convergent)

import RoutingLib.Routing.BellmanFord.Asynchronous as BellmanFord
open import RoutingLib.Routing.BellmanFord.ConvergenceConditions

import RoutingLib.Routing.BellmanFord.Asynchronous.DistanceVector.Convergence.StrictlyContracting as DistanceVectorResults
import RoutingLib.Routing.BellmanFord.Asynchronous.PathVector.Convergence.StrictlyContracting as PathVectorResults


module RoutingLib.Routing.BellmanFord.Asynchronous.Results
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) where

open Model algebra using (Network)
open BellmanFord algebra using (δ∥)

--------------------------------------------------------------------------------
-- Theorem 1
--
-- The asynchronous state function δ is always guaranteed to converge
-- asynchronously over any finite, strictly increasing routing algebra.

module _ (conditions : IsFiniteStrictlyIncreasingRoutingAlgebra algebra) where

  open IsFiniteStrictlyIncreasingRoutingAlgebra conditions

  finiteStrictlyIncr-converges : ∀ {n} (network : Network n) → Convergent (δ∥ network)
  finiteStrictlyIncr-converges network = ultra⇒convergent ultrametricConditions
    where open DistanceVectorResults isRoutingAlgebra isFinite isStrictlyIncreasing network

--------------------------------------------------------------------------------
-- Theorem 2
--
-- The asynchronous state function δ is always guaranteed to converge over any
-- strictly increasing path algebra.

module _ (conditions : IsIncreasingPathAlgebra algebra) where

  open IsIncreasingPathAlgebra conditions
  
  incrPaths-converges :  ∀ {n} (network : Network n) → Convergent (δ∥ network)
  incrPaths-converges {zero}  network = |0|-convergent (δ∥ network)
  incrPaths-converges {suc n} network = ultra⇒convergent ultrametricConditions
    where open PathVectorResults (isCertified (suc n)) isStrictlyIncreasing network (s≤s z≤n)
