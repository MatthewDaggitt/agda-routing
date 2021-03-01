open import Level
open import Data.Nat using (ℕ; _+_)
open import Data.Fin.Subset using (Subset)
open import Data.Product using (_×_)

open import RoutingLib.Relation.Unary.Indexed using (Uᵢ)

open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule using (Epoch)
import RoutingLib.Iteration.Asynchronous.Dynamic as Iteration
open import RoutingLib.Routing.Algebra
import RoutingLib.Routing as Routing

module RoutingLib.Routing.VectorBased.Convergence.Definitions
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  where

open Routing algebra using (Network)
open import RoutingLib.Routing.VectorBased.Synchronous algebra using (σ)
open import RoutingLib.Routing.VectorBased.Asynchronous algebra using (F∥)

private
  variable
    p : Level
  
------------------------------------------------------------------------
-- Convergence definitions

-- A routing algebra is partially convergent over some predicate P if the
-- iteration converges over all networks satisfying predicate P.

PartiallyConvergent : (∀ {n} → Network n → (Epoch × Subset n) → Set p) → Set _
PartiallyConvergent P = ∀ {n} (N : Network n) → Iteration.PartiallyConvergent (F∥ N) Uᵢ (P N)

-- A routing algebra is convergent if the iteration converges for all networks.

Convergent : Set _
Convergent = ∀ {n} (N : Network n) → Iteration.Convergent (F∥ N)

-- A routing algebra is synchronously convergent i

SynchronouslyConvergesIn : (ℕ → ℕ) → Set _
SynchronouslyConvergesIn f = ∀ {n : ℕ} (open Routing algebra n)
  (A : AdjacencyMatrix) (X : RoutingMatrix) →
  ∀ t → σ A (f n + t) X ≈ₘ σ A (f n) X
