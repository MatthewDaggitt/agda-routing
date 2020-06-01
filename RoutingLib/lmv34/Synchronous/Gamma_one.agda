open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
open import RoutingLib.Routing as Routing using (AdjacencyMatrix)
import RoutingLib.lmv34.Synchronous.Gamma_one.Algebra as Gamma_one_Algebra

module RoutingLib.lmv34.Synchronous.Gamma_one
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  {n} (A : AdjacencyMatrix algebra n)
  where

open Routing algebra n renaming (I to M)
open RawRoutingAlgebra algebra
open Gamma_one_Algebra isRoutingAlgebra n

------------------------------------
-- State model

Γ₁-State : Set a
Γ₁-State = RoutingVector

------------------------------------
-- Computation model

Γ₁ : Γ₁-State → Γ₁-State
Γ₁ V = A 〚 V 〛 ⊕ᵥ ~ M
