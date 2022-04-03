--------------------------------------------------------------------------------
-- Agda routing library
--
-- The top-level results on the convergence of the asynchronous vector-based
-- routing protocols.
--------------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n; _^_)
open import Level using (Level)

open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence
  using (completeConvergence)

open import RoutingLib.Routing.Basics.Network.Cycles using (TopologyIsFree; strIncr⇒alwaysFree)
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.Certification
open import RoutingLib.Routing.Algebra.Properties.PathAlgebra
open import RoutingLib.Routing.Algebra.Simulation using (_Simulates_)
import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Proof as Convergence
import RoutingLib.Routing.VectorBased.Convergence.Simulation as Simulation
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.Properties as PathVectorProperties
open import RoutingLib.Routing.VectorBased.Synchronous.PathVector.Convergence.Step6_Proof

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
  (strIncr⇒alwaysFree _ routingAlg strIncr N)

--------------------------------------------------------------------------------
-- Path vector protocols

module _ (isRoutingAlgebra : IsRoutingAlgebra A)
         (isPathAlgebra : IsPathAlgebra A)
         where

  private
    isCertifiedPathAlgebra = certifiedPathAlgebra isPathAlgebra
    module _ {n : ℕ} where
      open PathVectorProperties isRoutingAlgebra (isCertifiedPathAlgebra n) public
        renaming (𝑪ₘ′ to Consistent)
    
  -- For any path algebra the asynchronous iteration δ is always guaranteed
  -- to converge over any free network.
  paths⇒convergentOverFreeNetworks : PartiallyConvergent A (TopologyIsFree A)
  paths⇒convergentOverFreeNetworks =
    Convergence.paths⇒convergentOverFreeNetworks isRoutingAlgebra isPathAlgebra

  -- If the path algebra is increasing (or equivalently strictly increasing) then
  -- the asynchronous iteration δ is guaranteed to converge over any network.
  incrPaths⇒convergent : IsIncreasing A → Convergent A
  incrPaths⇒convergent incr N = completeConvergence
    (paths⇒convergentOverFreeNetworks N) _
    (strIncr⇒alwaysFree _ isRoutingAlgebra (incr⇒strIncr isRoutingAlgebra isPathAlgebra incr) N)

  -- If the path algebra is increasing then the synchronous iteration σ
  -- is guaranteed to converge in n² steps over any adjacency matrix.
  incrPaths⇒syncConvergesIn-n² : IsIncreasing A → SynchronouslyConvergesIn A (λ n → n ^ 2)
  incrPaths⇒syncConvergesIn-n² incr n@{suc _} =
    λ A → increasing⇒n²-convergence isRoutingAlgebra (isCertifiedPathAlgebra n) A incr

  -- If the path algebra is increasing *and* distributive then the synchronous iteration
  -- σ is guaranteed to converge in n steps over any adjacency matrix when starting from
  -- a state that is consistent with the adjacency matrix.
  incrPaths+distrib⇒syncConvergesIn-n-whenConsistent : IsIncreasing A →
                                                       IsDistributive A →
                                                       PartiallySynchronouslyConvergesIn A (λ n → n) Consistent
  incrPaths+distrib⇒syncConvergesIn-n-whenConsistent incr distrib n@{suc _} =
    λ A → increasing+distrib⇒n-convergence isRoutingAlgebra (isCertifiedPathAlgebra n) A incr distrib
