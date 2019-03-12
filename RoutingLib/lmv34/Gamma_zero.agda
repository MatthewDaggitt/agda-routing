open import Data.Nat using (ℕ; zero; suc)
open import Level using () renaming (suc to lsuc)

open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra)
open import RoutingLib.Routing as Routing using (AdjacencyMatrix)
import RoutingLib.lmv34.Gamma_zero.Algebra as Gamma_zero_Algebra

module RoutingLib.lmv34.Gamma_zero
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n} (A : AdjacencyMatrix algebra n)
  where

open Routing algebra n
open RawRoutingAlgebra algebra
open Gamma_zero_Algebra algebra n

------------------------------------
-- State model

record Γ₀-State : Set a where
  field
    Y : RoutingMatrix

------------------------------------
-- Computation model

Γ₀ : RoutingMatrix → RoutingMatrix
Γ₀ Y = A 〔 Y 〕 ⊕ₘ I

Γ₀-Model : Γ₀-State → Γ₀-State
Γ₀-Model State = record { Y = Γ₀ (Γ₀-State.Y State) }
