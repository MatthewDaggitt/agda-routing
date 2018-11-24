open import Data.Nat using (zero; suc; s≤s; z≤n)

open import RoutingLib.Iteration.Asynchronous.Dynamic using (Convergent)
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Theorems
  using (UltrametricConditions; ultra⇒convergent; |0|-convergent)

import RoutingLib.Routing as Routing
open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.VectorBased.Asynchronous as VectorBased
open import RoutingLib.Routing.VectorBased.ConvergenceConditions
import RoutingLib.Routing.VectorBased.Asynchronous.DistanceVector.Convergence.StrictlyContracting as DistanceVectorResults
import RoutingLib.Routing.VectorBased.Asynchronous.PathVector.Convergence.StrictlyContracting as PathVectorResults

module RoutingLib.Routing.VectorBased.Asynchronous.Results
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) where

open Routing algebra using (Network)
open VectorBased algebra using (F∥)

--------------------------------------------------------------------------------
-- Theorem 1
--
-- The asynchronous state function δ is always guaranteed to converge
-- asynchronously over any finite, strictly increasing routing algebra.

module _ (conditions : IsFiniteStrictlyIncreasingRoutingAlgebra algebra) where

  open IsFiniteStrictlyIncreasingRoutingAlgebra conditions

  finiteStrictlyIncr-converges : ∀ {n} (network : Network n) → Convergent (F∥ network)
  finiteStrictlyIncr-converges network = ultra⇒convergent (ultrametricConditions network)
    where open DistanceVectorResults isRoutingAlgebra isFinite isStrictlyIncreasing

--------------------------------------------------------------------------------
-- Theorem 2
--
-- The asynchronous state function δ is always guaranteed to converge over any
-- strictly increasing path algebra.

module _ (conditions : IsIncreasingPathAlgebra algebra) where

  open IsIncreasingPathAlgebra conditions
  
  incrPaths-converges :  ∀ {n} (network : Network n) → Convergent (F∥ network)
  incrPaths-converges {zero}  network = |0|-convergent (F∥ network)
  incrPaths-converges {suc n} network = ultra⇒convergent ultrametricConditions
    where open PathVectorResults (isCertified (suc n)) isStrictlyIncreasing network (s≤s z≤n)
