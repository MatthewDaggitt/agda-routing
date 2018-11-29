open import Data.Nat using (zero; suc; s≤s; z≤n)

open import RoutingLib.Iteration.Asynchronous.Dynamic using (Convergent)
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence
  using (UltrametricConditions; ultra⇒convergent; |0|-convergent)

import RoutingLib.Routing as Routing
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.Properties.PathAlgebra
open import RoutingLib.Routing.Algebra.Certification
import RoutingLib.Routing.VectorBased.Asynchronous as VectorBased
import RoutingLib.Routing.VectorBased.Asynchronous.DistanceVector.Convergence.StrictlyContracting as DistanceVectorResults
import RoutingLib.Routing.VectorBased.Asynchronous.PathVector.Convergence.StrictlyContracting as PathVectorResults

module RoutingLib.Routing.VectorBased.Asynchronous.Convergence
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) where

open Routing algebra using (Network)
open VectorBased algebra using (F∥)

--------------------------------------------------------------------------------
-- Definition of correctness

AlwaysConvergent : Set _
AlwaysConvergent = ∀ {n} (network : Network n) → Convergent (F∥ network)

--------------------------------------------------------------------------------
-- Theorem 1
--
-- The asynchronous state function δ is always guaranteed to converge
-- asynchronously over any finite, strictly increasing routing algebra. This
-- therefore applies to distance vector protocols.

finiteStrictlyIncr-converges : IsRoutingAlgebra algebra →
                               IsFinite algebra →
                               IsStrictlyIncreasing algebra →
                               AlwaysConvergent
finiteStrictlyIncr-converges routingAlg finite strIncr network =
  ultra⇒convergent (DistanceVectorResults.ultrametricConditions
    routingAlg finite strIncr network)

--------------------------------------------------------------------------------
-- Theorem 2
--
-- The asynchronous state function δ is always guaranteed to converge over any
-- strictly increasing path algebra. This therefore applies to path vector
-- algebras.

incrPaths-converges : IsRoutingAlgebra algebra →
                      IsPathAlgebra algebra →
                      IsIncreasing algebra →
                      AlwaysConvergent
incrPaths-converges _          _       _    {zero}  network = |0|-convergent (F∥ network)
incrPaths-converges routingAlg pathAlg incr {suc n} network =
  ultra⇒convergent (PathVectorResults.ultrametricConditions
    routingAlg (certifiedPathAlgebra pathAlg (suc n)) (incr⇒strIncr routingAlg pathAlg incr) network (s≤s z≤n))
