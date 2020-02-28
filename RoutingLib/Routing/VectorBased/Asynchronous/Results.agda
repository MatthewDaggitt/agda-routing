--------------------------------------------------------------------------------
-- Agda routing library
--
-- The top-level results on the convergence of the asynchronous vector-based
-- routing protocols.
--------------------------------------------------------------------------------

module RoutingLib.Routing.VectorBased.Asynchronous.Results where

open import Data.Nat using (zero; suc; s≤s; z≤n)
open import Level using (Level)

open import RoutingLib.Routing using (Network)
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.Properties.PathAlgebra
open import RoutingLib.Routing.Algebra.Simulation using (_Simulates_)
open import RoutingLib.Routing.Network.Definitions using (Free)
open import RoutingLib.Routing.Network.Properties using (strIncr⇒free)
import RoutingLib.Routing.VectorBased.Asynchronous.Simulation as Simulation
import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Proof as Convergence

private
  variable
    a b c d ℓ₁ ℓ₂ : Level
    A : RawRoutingAlgebra a b ℓ₁
    B : RawRoutingAlgebra c d ℓ₂

--------------------------------------------------------------------------------
-- Re-export convergence definitions

open import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Definitions public

--------------------------------------------------------------------------------
-- Bisimilarity

-- If an algebra is always convergent then any algebra simulated by it is also
-- convergent

simulate : A Simulates B → Convergent A → Convergent B
simulate A⇉B conv = Simulation.simulate A⇉B conv

--------------------------------------------------------------------------------
-- Distance vector protocols

-- If the routing algebra is finite then the asynchronous iteration δ is
-- guaranteed to converge over any free network.

finite⇒convergentOverFreeNetworks : IsRoutingAlgebra A →
                                    IsFinite A →
                                    PartiallyConvergent A (λ N → Free A N)
finite⇒convergentOverFreeNetworks routingAlg =
  Convergence.finite⇒convergentOverFreeNetworks routingAlg

-- If the routing algebra if finite and strictly increasing then the asynchronous
-- iteration δ is guaranteed to converge over any network.

finite+strictlyIncr⇒convergent : IsRoutingAlgebra A →
                                 IsFinite A →
                                 IsStrictlyIncreasing A →
                                 Convergent A
finite+strictlyIncr⇒convergent routingAlg finite strIncr N =
  finite⇒convergentOverFreeNetworks routingAlg finite (strIncr⇒free _ N routingAlg strIncr)

--------------------------------------------------------------------------------
-- Path vector protocols

-- For any path algebra the asynchronous iteration δ is always guaranteed
-- to converge over any free network.

paths⇒convergentOverFreeNetworks : IsRoutingAlgebra A →
                                   IsPathAlgebra A →  
                                   PartiallyConvergent A (λ N → Free A N)
paths⇒convergentOverFreeNetworks = Convergence.paths⇒convergentOverFreeNetworks

-- If the path algebra is increasing (or equivalently strictly increasing) then
-- the asynchronous iteration δ is guaranteed to converge over any network.

incrPaths⇒convergent : IsRoutingAlgebra A →
                       IsPathAlgebra A →
                       IsIncreasing A →
                       Convergent A
incrPaths⇒convergent routingAlg pathAlg incr N =
  paths⇒convergentOverFreeNetworks routingAlg pathAlg
    (strIncr⇒free _ N routingAlg
      (incr⇒strIncr routingAlg pathAlg incr))
