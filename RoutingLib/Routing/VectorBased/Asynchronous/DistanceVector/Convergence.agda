--------------------------------------------------------------------------------
-- Agda routing library
--
-- Proof that the metrics associated with a strictly increasing finite routing
-- algebra are strictly contracting in the right ways so as to ensure that
-- F∥ is an asynchronously metrically contracting operator (AMCO).
--------------------------------------------------------------------------------

open import RoutingLib.Routing.Network using (Network; IsFree)
open import RoutingLib.Routing.Algebra
open import RoutingLib.Function.Reasoning

module RoutingLib.Routing.VectorBased.Asynchronous.DistanceVector.Convergence
  {a b ℓ}
  {alg : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra alg)
  (isFinite : IsFinite alg)
  {n} (N : Network alg n)
  (N-free : IsFree alg N)
  where

open import RoutingLib.Routing.VectorBased.Asynchronous alg N
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence using (AMCO)
open import RoutingLib.Routing.VectorBased.Asynchronous.DistanceVector.Convergence.RouteDistanceFunction isRoutingAlgebra
open import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.AMCO alg isRoutingAlgebra N
open import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.HeightFunction alg
open import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.ExtensionRespectingOrder alg
open import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.RouteDistanceFunction isRoutingAlgebra

F∥-AMCO : AMCO F∥
F∥-AMCO = begin⟨ isFinite ⟩
  ∴ IsFinite alg                                   $⟨ (λ fin e p → <ᶠ-extensionRespectingOrder (Aₜ e p) isRoutingAlgebra fin (N-free e p)) ⟩
  ∴ (∀ e p → ExtensionRespectingOrder (Aₜ e p) _)  $⟨ (λ ero e p → extRespOrder⇒heightFunction (Aₜ e p) (ero e p) isFinite) ⟩
  ∴ (∀ e p → HeightFunction (Aₜ e p))              $⟨ (λ hf e p → routeDistanceFunction (Aₜ e p) (hf e p)) ⟩
  ∴ (∀ e p → RouteDistanceFunction (Aₜ e p))       $⟨ amco ⟩
  ∴ AMCO F∥                                        ∎
