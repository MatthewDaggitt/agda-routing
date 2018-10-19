open import Data.Nat using (ℕ; zero; suc; _⊔_)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (length)
open import Data.List.Any using (index)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Data.Table using (max; zipWith)

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.RoutingAlgebra
import RoutingLib.Routing.Algebra.RoutingAlgebra.FiniteProperties as FiniteProperties
import RoutingLib.Routing.Model as Model

module RoutingLib.Routing.BellmanFord.Synchronous.DistanceVector.Convergence.Metrics
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (isFinite : IsFinite algebra)
  where

open Model algebra
open RawRoutingAlgebra algebra
open FiniteProperties isRoutingAlgebra isFinite hiding (H)
open FiniteProperties isRoutingAlgebra isFinite using (H) public 

-- Some notational shorthand for the index of route u in the list of routes
i[_] : Route → Fin (length routes)
i[ u ] = index (∈-routes u)

-- The height of an element x is the number of
-- elements above it in the order (i.e. |{y | x ≤ y}|)
h : Route → ℕ
h x = suc (toℕ (i[ x ]))

-- The distance between two routes
d : Route → Route → ℕ
d x y with x ≟ y
... | yes _ = zero
... | no  _ = h x ⊔ h y

-- The distance between two routing tables
dₜ : ∀ {n} → RoutingTable n → RoutingTable n → ℕ
dₜ x y = max 0 (zipWith d x y)

-- The distance between two routing matrices
D : ∀ {n} → RoutingMatrix n → RoutingMatrix n → ℕ
D X Y = max 0 (zipWith dₜ X Y)
