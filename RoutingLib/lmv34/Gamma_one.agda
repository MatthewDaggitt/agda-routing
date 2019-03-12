open import Data.Nat using (ℕ; zero; suc)
open import Level using () renaming (suc to lsuc)
open import Data.List using (List)

open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
open import RoutingLib.Routing as Routing using (AdjacencyMatrix)
import RoutingLib.lmv34.Gamma_one.Algebra as Gamma_one_Algebra

module RoutingLib.lmv34.Gamma_one
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  {n} (A : AdjacencyMatrix algebra n)
  where

open Routing algebra n renaming (I to M)
open RawRoutingAlgebra algebra
open Gamma_one_Algebra isRoutingAlgebra n

------------------------------------
-- State model

record Γ₁-State : Set a where
  field
    V : RoutingVector

------------------------------------
-- Computation model

Γ₁ : RoutingVector → RoutingVector
Γ₁ V = A 〚 V 〛 ⊕ᵥ ~ M

Γ₁-Model : Γ₁-State → Γ₁-State
Γ₁-Model State = record { V = Γ₁ (Γ₁-State.V State) }
