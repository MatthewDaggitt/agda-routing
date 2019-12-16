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

module RoutingLib.Routing.VectorBased.Asynchronous.PathVector.Convergence
  {a b ℓ}
  {alg : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra alg)
  (isPathAlgebra : IsPathAlgebra alg)
  {n} {N : Network alg n}
  (N-free : IsFree alg N)
  where

open import Data.Nat using (_≟_)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence using (AMCO; |0|-convergent)

open import RoutingLib.Routing.Algebra.Certification
open import RoutingLib.Routing.VectorBased.Asynchronous alg N hiding (IsFree)
open import RoutingLib.Routing.VectorBased.Asynchronous.PathVector.Convergence.RouteDistanceFunction isRoutingAlgebra
open import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.AMCO alg isRoutingAlgebra N
open import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.HeightFunction alg
open import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.ExtensionRespectingOrder alg
open import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.RouteDistanceFunction isRoutingAlgebra

isCertifiedPathAlgebra : IsCertifiedPathAlgebra alg n
isCertifiedPathAlgebra = certifiedPathAlgebra isPathAlgebra n

F∥-AMCO : AMCO F∥
F∥-AMCO = begin⟨ N-free ⟩
  ∴ IsFree alg N                                   $⟨ ((λ free e p → <ᶠ-extensionRespectingOrder (Aₜ e p) isRoutingAlgebra {!!} (N-free e p))) ⟩
  ∴ (∀ e p → ExtensionRespectingOrder (Aₜ e p) _)  $⟨ (λ ero e p → extRespOrder⇒heightFunction (Aₜ e p) (ero e p) {!!}) ⟩
  ∴ (∀ e p → HeightFunction (Aₜ e p))              $⟨ (λ hf e p → routeDistanceFunction isCertifiedPathAlgebra (Aₜ e p) {!1≤n!}) ⟩
  ∴ (∀ e p → RouteDistanceFunction (Aₜ e p))       $⟨ amco ⟩
  ∴ AMCO F∥                                        ∎
