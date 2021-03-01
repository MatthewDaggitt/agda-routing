--------------------------------------------------------------------------------
-- Agda routing library
--
-- The top-level results on the convergence of the asynchronous vector-based
-- routing protocols.
--------------------------------------------------------------------------------

open import Data.Nat using (zero; suc; s≤s; z≤n; _^_)
open import Level using (Level)

open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence
  using (completeConvergence)

open import RoutingLib.Routing using (Network)
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.Certification
open import RoutingLib.Routing.Algebra.Properties.PathAlgebra
open import RoutingLib.Routing.Algebra.Simulation using (_Simulates_)
open import RoutingLib.Routing.Network.Definitions using (TopologyIsFree)
open import RoutingLib.Routing.Algebra.Consequences using (strIncr⇒free)
import RoutingLib.Routing.VectorBased.Convergence.Simulation as Simulation
import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Proof as Convergence
open import RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Step5_Proof

module RoutingLib.Routing.VectorBased.Convergence.Results where

private
  variable
    a b c d ℓ₁ ℓ₂ : Level
    A : RawRoutingAlgebra a b ℓ₁
    B : RawRoutingAlgebra c d ℓ₂

--------------------------------------------------------------------------------
-- Re-export convergence definitions

open import RoutingLib.Routing.VectorBased.Convergence.Definitions public

--------------------------------------------------------------------------------
-- Bisimilarity

-- If an algebra is always convergent then any algebra simulated by it is also
-- convergent

simulate-convergent : A Simulates B → Convergent A → Convergent B
simulate-convergent = Simulation.convergent

simulate-syncConvergesIn : A Simulates B → ∀ f →
                           SynchronouslyConvergesIn A f →
                           SynchronouslyConvergesIn B f
simulate-syncConvergesIn = Simulation.syncConvergesIn

--------------------------------------------------------------------------------
-- Distance vector protocols

-- If the routing algebra is finite then the asynchronous iteration δ is
-- guaranteed to converge over any free network.

finite⇒convergentOverFreeNetworks : IsRoutingAlgebra A →
                                    IsFinite A →
                                    PartiallyConvergent A (TopologyIsFree A)
finite⇒convergentOverFreeNetworks routingAlg =
  Convergence.finite⇒convergentOverFreeNetworks routingAlg

-- If the routing algebra if finite and strictly increasing then the asynchronous
-- iteration δ is guaranteed to converge over any network.

finite+strictlyIncr⇒convergent : IsRoutingAlgebra A →
                                 IsFinite A →
                                 IsStrictlyIncreasing A →
                                 Convergent A
finite+strictlyIncr⇒convergent routingAlg finite strIncr N = completeConvergence
  (finite⇒convergentOverFreeNetworks routingAlg finite N) _
  (strIncr⇒free routingAlg strIncr N)

--------------------------------------------------------------------------------
-- Path vector protocols

-- For any path algebra the asynchronous iteration δ is always guaranteed
-- to converge over any free network.

paths⇒convergentOverFreeNetworks : IsRoutingAlgebra A →
                                   IsPathAlgebra A →  
                                   PartiallyConvergent A (TopologyIsFree A)
paths⇒convergentOverFreeNetworks = Convergence.paths⇒convergentOverFreeNetworks

-- If the path algebra is increasing (or equivalently strictly increasing) then
-- the asynchronous iteration δ is guaranteed to converge over any network.

incrPaths⇒convergent : IsRoutingAlgebra A →
                       IsPathAlgebra A →
                       IsIncreasing A →
                       Convergent A
incrPaths⇒convergent routingAlg pathAlg incr N = completeConvergence
  (paths⇒convergentOverFreeNetworks routingAlg pathAlg N) _
  (strIncr⇒free routingAlg (incr⇒strIncr routingAlg pathAlg incr) N)

-- If the path algebra is increasing then the synchronous iteration σ
-- is guaranteed to converge in n² steps over any adjacency matrix.

incrPaths⇒syncConvergesIn-n² : IsRoutingAlgebra A →
                               IsPathAlgebra A →
                               IsIncreasing A →
                               SynchronouslyConvergesIn A (λ n → n ^ 2)
incrPaths⇒syncConvergesIn-n² routingAlg pathAlg incr n@{suc _} =
  n²-convergence routingAlg (certifiedPathAlgebra pathAlg n) incr
