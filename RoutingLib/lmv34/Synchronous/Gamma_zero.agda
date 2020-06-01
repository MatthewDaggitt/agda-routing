open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra)
open import RoutingLib.Routing as Routing using (AdjacencyMatrix)
import RoutingLib.lmv34.Synchronous.Gamma_zero.Algebra as Gamma_zero_Algebra

module RoutingLib.lmv34.Synchronous.Gamma_zero
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n} (A : AdjacencyMatrix algebra n)
  where

open Routing algebra n renaming (I to M)
open Gamma_zero_Algebra algebra n

------------------------------------
-- State model

Γ₀-State : Set a
Γ₀-State = RoutingMatrix

------------------------------------
-- Computation model

Γ₀ : Γ₀-State → Γ₀-State
Γ₀ Y = A 〔 Y 〕 ⊕ₘ M
