open import Level
open import Data.Fin.Subset using (Subset)
open import Data.Product using (_×_)

open import RoutingLib.Relation.Unary.Indexed using (Uᵢ)

open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule using (Epoch)
import RoutingLib.Iteration.Asynchronous.Dynamic as Iteration
open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Definitions
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  where

open import RoutingLib.Routing algebra hiding (Epoch)
open import RoutingLib.Routing.VectorBased.Asynchronous algebra hiding (Epoch)

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
