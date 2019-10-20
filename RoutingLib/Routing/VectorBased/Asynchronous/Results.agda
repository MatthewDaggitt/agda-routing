--------------------------------------------------------------------------------
-- Agda routing library
--
-- The top-level results on the convergence of the asynchronous vector-based
-- routing protocols.
--------------------------------------------------------------------------------

module RoutingLib.Routing.VectorBased.Asynchronous.Results where

open import Data.Nat using (zero; suc; s≤s; z≤n)
open import Level using (Level)

open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence
  using (AMCO; AMCO⇒convergent; |0|-convergent)

open import RoutingLib.Routing.Network using (Network; IsFree)
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.Properties.PathAlgebra
open import RoutingLib.Routing.Algebra.Certification
open import RoutingLib.Routing.Algebra.Simulation using (_Simulates_)
open import RoutingLib.Routing.VectorBased.Asynchronous using (F∥)
import RoutingLib.Routing.VectorBased.Asynchronous.Simulation as Simulation
import RoutingLib.Routing.VectorBased.Asynchronous.DistanceVector.Convergence as DV
open import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Definitions

private
  variable
    a b c d ℓ₁ ℓ₂ : Level
    A : RawRoutingAlgebra a b ℓ₁
    B : RawRoutingAlgebra c d ℓ₂

--------------------------------------------------------------------------------
-- Finite strictly increasing distance vector protocols
--
-- The asynchronous state function δ is always guaranteed to converge
-- asynchronously over any finite, strictly increasing routing algebra. This
-- therefore applies to distance vector protocols.

finite⇒convergentOverFreeNetworks : IsRoutingAlgebra A →
                                    IsFinite A →
                                    PartiallyConvergent A (IsFree A)
finite⇒convergentOverFreeNetworks routingAlg finite N isFree =
  AMCO⇒convergent (DV.F∥-AMCO routingAlg finite N isFree)

finite+strictlyIncr⇒convergent : IsRoutingAlgebra A →
                                 IsFinite A →
                                 IsStrictlyIncreasing A →
                                 Convergent A
finite+strictlyIncr⇒convergent routingAlg finite strIncr N =
  finite⇒convergentOverFreeNetworks routingAlg finite N {!!}

--------------------------------------------------------------------------------
-- Strictly increasing path vector protocols
--
-- The asynchronous state function δ is always guaranteed to converge over any
-- strictly increasing path algebra. This therefore applies to path vector
-- algebras.

{-
incrPaths⇒convergent : IsRoutingAlgebra A →
                       IsPathAlgebra A →
                       IsIncreasing A →
                       AlwaysConvergent A
incrPaths⇒convergent _          _       _    {zero}  N = |0|-convergent (F∥ _ N)
incrPaths⇒convergent routingAlg pathAlg incr {suc n} N = AMCO⇒convergent
  (PVResults.F∥-isAMCO
    routingAlg
    (certifiedPathAlgebra pathAlg (suc n))
    (incr⇒strIncr routingAlg pathAlg incr)
    N (s≤s z≤n))

--------------------------------------------------------------------------------
-- Bisimilarity
--
-- If an algebra is always convergent then any algebra simulated by it is also
-- convergent

simulate : A Simulates B →
           AlwaysConvergent A →
           AlwaysConvergent B
simulate A⇉B conv = Simulation.simulate A⇉B conv
-}
