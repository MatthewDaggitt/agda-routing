open import Data.Nat using (zero; suc; s≤s; z≤n)

open import RoutingLib.Iteration.Asynchronous.Dynamic using (Convergent)
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence
  using (UltrametricConditions; ultra⇒convergent; |0|-convergent)

import RoutingLib.Routing as Routing
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.Properties.PathAlgebra
open import RoutingLib.Routing.Algebra.Certification
open import RoutingLib.Routing.Algebra.Bisimulation as Algebra using (Bisimilar)
import RoutingLib.Routing.VectorBased.Asynchronous as VectorBased
import RoutingLib.Routing.VectorBased.Asynchronous.DistanceVector.Convergence.StrictlyContracting as DistanceVectorResults
import RoutingLib.Routing.VectorBased.Asynchronous.PathVector.Convergence.StrictlyContracting as PathVectorResults

module RoutingLib.Routing.VectorBased.Asynchronous.Convergence where

open Routing using (Network)
open VectorBased using (F∥)

--------------------------------------------------------------------------------
-- Definition of correctness

AlwaysConvergent : ∀ {a b ℓ} → RawRoutingAlgebra a b ℓ → Set _
AlwaysConvergent A = ∀ {n} (network : Network A n) → Convergent (F∥ A network)

--------------------------------------------------------------------------------
-- Finite strictly increasing distance vector protocols
--
-- The asynchronous state function δ is always guaranteed to converge
-- asynchronously over any finite, strictly increasing routing algebra. This
-- therefore applies to distance vector protocols.

finiteStrictlyIncr-converges : ∀ {a b ℓ} {A : RawRoutingAlgebra a b ℓ} →
                               IsRoutingAlgebra A →
                               IsFinite A →
                               IsStrictlyIncreasing A →
                               AlwaysConvergent A
finiteStrictlyIncr-converges routingAlg finite strIncr network =
  ultra⇒convergent (DistanceVectorResults.ultrametricConditions
    routingAlg finite strIncr network)

--------------------------------------------------------------------------------
-- Strictly increasing path vector protocols
--
-- The asynchronous state function δ is always guaranteed to converge over any
-- strictly increasing path algebra. This therefore applies to path vector
-- algebras.

incrPaths-converges : ∀ {a b ℓ} {A : RawRoutingAlgebra a b ℓ} →
                      IsRoutingAlgebra A →
                      IsPathAlgebra A →
                      IsIncreasing A →
                      AlwaysConvergent A
incrPaths-converges {A = A} _          _       _    {zero}  network = |0|-convergent (F∥ A network)
incrPaths-converges {A = A} routingAlg pathAlg incr {suc n} network =
  ultra⇒convergent (PathVectorResults.ultrametricConditions
    routingAlg (certifiedPathAlgebra pathAlg (suc n)) (incr⇒strIncr routingAlg pathAlg incr) network (s≤s z≤n))

--------------------------------------------------------------------------------
-- Bisimilarity
--
-- If an algebra is always convergent then all algebras that are bisimilar to it
-- are also convergent

bisimulate : ∀ {a b c d ℓ₁ ℓ₂}
             {A : RawRoutingAlgebra a b ℓ₁}
             {B : RawRoutingAlgebra c d ℓ₂} →
             Bisimilar A B →
             AlwaysConvergent A →
             AlwaysConvergent B
bisimulate A∼B conv = Algebra.bisimulate A∼B conv

