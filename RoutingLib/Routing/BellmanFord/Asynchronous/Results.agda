open import Data.Nat using (zero; suc; s≤s; z≤n; _≤_)
open import Function using (case_of_)

import RoutingLib.Routing.Model as Model
open import RoutingLib.Routing.Algebra
open import RoutingLib.Iteration.Asynchronous.Dynamic using (IsSafe)
open import RoutingLib.Iteration.Asynchronous.Dynamic.Properties using (0-IsSafe)
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Theorems using (UltrametricConditions; ultra⇒safety)

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

  finiteStrictlyIncr-converges : ∀ {n} (network : Network n) → IsSafe (δ∥ network)
  finiteStrictlyIncr-converges network = ultra⇒safety ultrametricConditions
    where open DistanceVectorResults isRoutingAlgebra isFinite isStrictlyIncreasing network

--------------------------------------------------------------------------------
-- Theorem 2
--
-- The asynchronous state function δ is always guaranteed to converge over any
-- strictly increasing path algebra.

module _ (conditions : IsIncreasingPathAlgebra algebra) where

  open IsIncreasingPathAlgebra conditions
  
  incrPaths-converges :  ∀ {n} (network : Network n) → IsSafe (δ∥ network)
  incrPaths-converges {n = zero}  network = 0-IsSafe (δ∥ network)
  incrPaths-converges {n = suc n} network = ultra⇒safety ultrametricConditions
    where open PathVectorResults (isCertifiedPathAlgebra (suc n)) isStrictlyIncreasing network (s≤s z≤n)
