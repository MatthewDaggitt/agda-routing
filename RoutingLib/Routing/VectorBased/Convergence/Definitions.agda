open import Level
open import Data.Nat using (ℕ; _+_)
open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset)
open import Data.Product using (_×_)
open import Relation.Unary using (Pred)

open import RoutingLib.Relation.Unary.Indexed using (Uᵢ)

open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule using (Epoch)
import RoutingLib.Iteration.Asynchronous.Dynamic as Iteration
open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.VectorBased.Convergence.Definitions
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  where

open import RoutingLib.Routing.Prelude algebra as Routing
  using (Network; Participants)
open import RoutingLib.Routing.VectorBased.Synchronous algebra using (σ)
open import RoutingLib.Routing.VectorBased.Asynchronous algebra using (F∥)

private
  variable
    p : Level
  
------------------------------------------------------------------------
-- Convergence definitions

-- A routing algebra is partially convergent over some predicate P if the
-- iteration converges over all networks satisfying predicate P.

PartiallyConvergent : (∀ {n} → Network n → (Epoch × Participants n) → Set p) → Set _
PartiallyConvergent P = ∀ {n} (N : Network n) → Iteration.PartiallyConvergent (F∥ N) Uᵢ (P N)

-- A routing algebra is convergent if the iteration converges for all networks.

Convergent : Set _
Convergent = ∀ {n} (N : Network n) → Iteration.Convergent (F∥ N)

-- A routing algebra is synchronously convergent i

SynchronouslyConvergesIn : (ℕ → ℕ) → Set _
SynchronouslyConvergesIn f = ∀ {n} (open Routing n)
  (A : AdjacencyMatrix) (X : RoutingMatrix) →
  ∀ t → σ A (f n + t) X ≈ₘ σ A (f n) X

PartiallySynchronouslyConvergesIn : (ℕ → ℕ) →
                                    ∀ {ℓ} (P : ∀ {n} (open Routing n) (A : AdjacencyMatrix) → Pred RoutingMatrix ℓ) → Set _
PartiallySynchronouslyConvergesIn f P = ∀ {n} (open Routing n)
  (A : AdjacencyMatrix) (X : RoutingMatrix) → P A X →
  ∀ t → σ A (f n + t) X ≈ₘ σ A (f n) X
