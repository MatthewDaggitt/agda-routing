open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Definitions
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  where

open import Level

open import RoutingLib.Routing algebra
open import RoutingLib.Routing.VectorBased.Asynchronous algebra
import RoutingLib.Iteration.Asynchronous.Dynamic as Iteration

private
  variable
    p : Level
  
------------------------------------------------------------------------
-- Convergence definitions

-- A routing algebra is partially convergent over some predicate P if the
-- iteration converges over all networks satisfying predicate P.

PartiallyConvergent : (∀ {n} → Network n → Set p) → Set _
PartiallyConvergent P = ∀ {n} {N : Network n} → P N → Iteration.Convergent (F∥ N)

-- A routing algebra is convergent if the iteration converges for all networks.

Convergent : Set _
Convergent = ∀ {n} (N : Network n) → Iteration.Convergent (F∥ N)
