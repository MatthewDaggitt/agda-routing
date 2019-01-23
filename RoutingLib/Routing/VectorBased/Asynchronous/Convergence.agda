--------------------------------------------------------------------------------
-- The top-level results on the convergence of the asynchronous vector-based
-- routing protocols.
--------------------------------------------------------------------------------

module RoutingLib.Routing.VectorBased.Asynchronous.Convergence where

open import Data.Nat using (zero; suc; s≤s; z≤n)

open import RoutingLib.Iteration.Asynchronous.Dynamic using (Convergent)
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence
  using (AMCO; AMCO⇒convergent; |0|-convergent)

open import RoutingLib.Routing using (Network)
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.Properties.PathAlgebra
open import RoutingLib.Routing.Algebra.Certification
open import RoutingLib.Routing.Algebra.Simulation using (Simulates)
open import RoutingLib.Routing.VectorBased.Asynchronous using (F∥)
import RoutingLib.Routing.VectorBased.Asynchronous.Simulation as Simulation
import RoutingLib.Routing.VectorBased.Asynchronous.DistanceVector.Convergence.StrictlyContracting
  as DVResults
import RoutingLib.Routing.VectorBased.Asynchronous.PathVector.Convergence.StrictlyContracting
  as PVResults

--------------------------------------------------------------------------------
-- Definition of correctness

AlwaysConvergent : ∀ {a b ℓ} → RawRoutingAlgebra a b ℓ → Set _
AlwaysConvergent A = ∀ {n} (N : Network A n) → Convergent (F∥ A N)

--------------------------------------------------------------------------------
-- Finite strictly increasing distance vector protocols
--
-- The asynchronous state function δ is always guaranteed to converge
-- asynchronously over any finite, strictly increasing routing algebra. This
-- therefore applies to distance vector protocols.

finiteStrictlyIncr⇒convergent : ∀ {a b ℓ} {A : RawRoutingAlgebra a b ℓ} →
                                IsRoutingAlgebra A →
                                IsFinite A →
                                IsStrictlyIncreasing A →
                                AlwaysConvergent A
finiteStrictlyIncr⇒convergent routingAlg finite strIncr network =
  AMCO⇒convergent (DVResults.F∥-isAMCO routingAlg finite strIncr network)

--------------------------------------------------------------------------------
-- Strictly increasing path vector protocols
--
-- The asynchronous state function δ is always guaranteed to converge over any
-- strictly increasing path algebra. This therefore applies to path vector
-- algebras.

incrPaths⇒convergent : ∀ {a b ℓ} {A : RawRoutingAlgebra a b ℓ} →
                       IsRoutingAlgebra A →
                       IsPathAlgebra A →
                       IsIncreasing A →
                       AlwaysConvergent A
incrPaths⇒convergent _          _       _    {zero}  N = |0|-convergent (F∥ _ N)
incrPaths⇒convergent routingAlg pathAlg incr {suc n} N =
  AMCO⇒convergent (PVResults.F∥-isAMCO
    routingAlg
    (certifiedPathAlgebra pathAlg (suc n))
    (incr⇒strIncr routingAlg pathAlg incr)
    N (s≤s z≤n))

--------------------------------------------------------------------------------
-- Bisimilarity
--
-- If an algebra is always convergent then any algebra simulated by it is also
-- convergent

simulate : ∀ {a b c d ℓ₁ ℓ₂}
             {A : RawRoutingAlgebra a b ℓ₁}
             {B : RawRoutingAlgebra c d ℓ₂} →
             Simulates A B →
             AlwaysConvergent A →
             AlwaysConvergent B
simulate A⇉B conv = Simulation.simulate A⇉B conv
