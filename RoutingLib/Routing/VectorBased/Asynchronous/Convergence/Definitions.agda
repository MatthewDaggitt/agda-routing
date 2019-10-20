

module RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Definitions where

open import Level

open import RoutingLib.Routing
open import RoutingLib.Routing.Network
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.VectorBased.Asynchronous

import RoutingLib.Iteration.Asynchronous.Dynamic as Iteration

-- A routing algebra is partially convergent over some predicate P if the
-- iteration converges over all networks satisfying predicate P.

PartiallyConvergent : ∀ {a b ℓ p} (A : RawRoutingAlgebra a b ℓ) → (∀ {n} → Network A n → Set p) → Set _
PartiallyConvergent A P = ∀ {n} (N : Network A n) → P N → Iteration.Convergent (F∥ A N)

-- A routing algebra is convergent if the iteration converges for all networks.

Convergent : ∀ {a b ℓ} → RawRoutingAlgebra a b ℓ → Set _
Convergent A = ∀ {n} (N : Network A n) → Iteration.Convergent (F∥ A N)
