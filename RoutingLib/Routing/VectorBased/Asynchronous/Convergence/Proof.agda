open import Level using (Level)

open import RoutingLib.Function.Reasoning

open import RoutingLib.Routing.Prelude using (Network; AdjacencyMatrix)
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.Certification
import RoutingLib.Routing.Algebra.Construct.Consistent as ConsistentRoutes
open import RoutingLib.Routing.Basics.Network.Cycles
open import RoutingLib.Routing.VectorBased.Asynchronous hiding (AdjacencyMatrix)
open import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Definitions
open import RoutingLib.Routing.VectorBased.Convergence.Definitions

import RoutingLib.Iteration.Asynchronous.Dynamic as Iteration
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence as Iteration using (PartialAMCO; AMCO; Uᵢ-validInitialSet)
import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step1_FreeImpliesERO as Step1
import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step2_EROImpliesHF as Step2
import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step3_HFImpliesDF_DistanceVector as Step3_DV
import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step3_HFImpliesDF_PathVector as Step3_PV
import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step4_DFImpliesAMCO as Step4

module RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Proof where

private
  variable
    a b ℓ : Level
    algebra : RawRoutingAlgebra a b ℓ

private
  finite+cycleFree⇒routeDistanceFunction : IsRoutingAlgebra algebra →
                                           IsFinite algebra →
                                           ∀ {n} {A : AdjacencyMatrix algebra n} →
                                           .(IsFreeAdjacencyMatrix algebra A) →
                                           RouteDistanceFunction algebra A
  finite+cycleFree⇒routeDistanceFunction {algebra = algebra} isRoutingAlgebra fin {n} {A} free =
    begin⟨ Step1.<ᶠ-extensionRespectingOrder isRoutingAlgebra A fin free ⟩
    ∴ ExtensionRespectingOrder algebra A _  $⟨ Step2.heightFunction algebra fin A ⟩
    ∴ HeightFunction algebra A              $⟨ Step3_DV.routeDistanceFunction isRoutingAlgebra A ⟩
    ∴ RouteDistanceFunction algebra A       ∎

finite⇒convergentOverFreeNetworks : IsRoutingAlgebra algebra →
                                    IsFinite algebra →
                                    PartiallyConvergent algebra (TopologyIsFree algebra)
finite⇒convergentOverFreeNetworks {algebra = algebra} isRoutingAlgebra finite N =
  Iteration.AMCO⇒convergent-partial (Uᵢ-validInitialSet _)
    (Step4.partialAMCO isRoutingAlgebra N
      (finite+cycleFree⇒routeDistanceFunction isRoutingAlgebra finite))

paths⇒convergentOverFreeNetworks : IsRoutingAlgebra algebra →
                                   IsPathAlgebra algebra →
                                   PartiallyConvergent algebra (TopologyIsFree algebra)                      
paths⇒convergentOverFreeNetworks {algebra = algebra} isRoutingAlgebra isPathAlgebra {n} N =
  Iteration.AMCO⇒convergent-partial (Uᵢ-validInitialSet _)
    (Step4.partialAMCO isRoutingAlgebra N
      λ free → Step3_PV.routeDistanceFunction isRoutingAlgebra isCertifiedPathAlgebra
        (finite+cycleFree⇒routeDistanceFunction isRoutingAlgebraᶜ isFiniteᶜ
          (freeᶜ free)))
  where
  isCertifiedPathAlgebra = certifiedPathAlgebra isPathAlgebra n
  
  module _ {e p} where
    open ConsistentRoutes isRoutingAlgebra isCertifiedPathAlgebra (Aₜ algebra N e p) public
