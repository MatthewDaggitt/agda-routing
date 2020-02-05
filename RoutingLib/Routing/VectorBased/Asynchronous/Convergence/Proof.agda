open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Proof
  where

open import Level using (Level)

open import RoutingLib.Function.Reasoning

open import RoutingLib.Routing using (Network; AdjacencyMatrix)
open import RoutingLib.Routing.Algebra.Certification
open import RoutingLib.Routing.Network.Definitions
open import RoutingLib.Routing.AdjacencyMatrix.Definitions
open import RoutingLib.Routing.VectorBased.Asynchronous hiding (AdjacencyMatrix; Aₜ)
open import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Definitions
open import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.InternalDefinitions

import RoutingLib.Iteration.Asynchronous.Dynamic as Iteration
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence as Iteration using (AMCO)
import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step1_FreeImpliesERO as Step1
import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step2_EROImpliesHF as Step2
import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step3_HFImpliesDF_DistanceVector as Step3_DV
import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step3_HFImpliesDF_PathVector as Step3_PV
import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step4_DFImpliesAMCO as Step4

private
  variable
    a b ℓ : Level
    algebra : RawRoutingAlgebra a b ℓ
    
  finite+cycleFree⇒routeDistanceFunction : IsRoutingAlgebra algebra →
                                           IsFinite algebra →
                                           ∀ {n} {A : AdjacencyMatrix algebra n} →
                                           CycleFree algebra A →
                                           RouteDistanceFunction algebra A
  finite+cycleFree⇒routeDistanceFunction {algebra = algebra} isRoutingAlgebra fin {n} {A} = begin⟨_⟩
    ∴ CycleFree algebra A                   $⟨ Step1.<ᶠ-extensionRespectingOrder isRoutingAlgebra A fin ⟩
    ∴ ExtensionRespectingOrder algebra A _  $⟨ Step2.heightFunction algebra fin A ⟩
    ∴ HeightFunction algebra A              $⟨ Step3_DV.routeDistanceFunction isRoutingAlgebra A ⟩
    ∴ RouteDistanceFunction algebra A       ∎

finite⇒convergentOverFreeNetworks : IsRoutingAlgebra algebra →
                                    IsFinite algebra →
                                    PartiallyConvergent algebra (Free algebra)
finite⇒convergentOverFreeNetworks {algebra = algebra} isRoutingAlgebra fin {n} {N} = begin⟨_⟩
  ∴ Free algebra N                                             $⟨ (λ free e p → finite+cycleFree⇒routeDistanceFunction isRoutingAlgebra fin (free e p)) ⟩
  ∴ (∀ e p → RouteDistanceFunction algebra (Aₜ algebra N e p)) $⟨ Step4.amco isRoutingAlgebra N ⟩
  ∴ AMCO (F∥ algebra N)                                        $⟨ Iteration.AMCO⇒convergent ⟩
  ∴ Iteration.Convergent (F∥ algebra N)                        ∎

paths⇒convergentOverFreeNetworks : IsRoutingAlgebra algebra →
                                   IsPathAlgebra algebra →
                                   PartiallyConvergent algebra (Free algebra)                                 
paths⇒convergentOverFreeNetworks {algebra = algebra} isRoutingAlgebra isPathAlgebra {n} {N} = begin⟨_⟩
  ∴ Free algebra N                                             $⟨ (λ free e p → finite+cycleFree⇒routeDistanceFunction isRoutingAlgebraᶜ isFiniteᶜ (cycleFreeᶜ (free e p))) ⟩
  ∴ (∀ e p → RouteDistanceFunction algebraᶜ (Aᶜ {e} {p}))      $⟨ (λ rdfᶜ e p → Step3_PV.routeDistanceFunction isRoutingAlgebra isCertifiedPathAlgebra (rdfᶜ e p)) ⟩
  ∴ (∀ e p → RouteDistanceFunction algebra (Aₜ algebra N e p)) $⟨ Step4.amco isRoutingAlgebra N ⟩
  ∴ AMCO (F∥ algebra N)                                        $⟨ Iteration.AMCO⇒convergent ⟩
  ∴ Iteration.Convergent (F∥ algebra N)                        ∎
  where
  isCertifiedPathAlgebra = certifiedPathAlgebra isPathAlgebra n
  
  module _ {e p} where
    open import RoutingLib.Routing.Algebra.Construct.Consistent isRoutingAlgebra isCertifiedPathAlgebra (Aₜ algebra N e p) public
