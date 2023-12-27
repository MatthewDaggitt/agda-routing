open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra)
open import RoutingLib.Routing.Prelude as RoutingPrelude using () renaming (AdjacencyMatrix to AdjacencyMatrix')

module RoutingLib.lmv34.Asynchronous.Omega_zero
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n} (A : AdjacencyMatrix' algebra n)
  where

open import Data.Fin using (Fin)
open import Data.Nat using (zero; suc; s≤s; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (≤-refl)
open import Induction.WellFounded using (Acc; acc)

open import RoutingLib.lmv34.Asynchronous.Omega_zero.Algebra algebra A
open import RoutingLib.lmv34.Synchronous.Gamma_zero algebra A
open import RoutingLib.Iteration.Asynchronous.Static.Schedule using (Schedule; 𝕋)

open RoutingPrelude algebra n using (RoutingMatrix)

--------------------------------------------------------------------------------
-- Implementation of Ω₀

-- We first define Ω₀ with an explicit accessible argument.
-- This is required to prove that the function terminates.

module _ (ψ : Schedule n) where
  open Schedule ψ

  Ω₀' : Γ₀-State → {t : 𝕋} → Acc _<_ t → Γ₀-State
  Ω₀' X {zero}  _         = X
  Ω₀' X {suc t} (acc rec) = [ Γ₀' X[β[t+1]] , X[t] ] α (suc t)
    where X[t] : RoutingMatrix
          X[t] = Ω₀' X (rec ≤-refl)
          X[β[t+1]] : Fin n → RoutingMatrix
          X[β[t+1]] i q j = Ω₀' X (rec (s≤s (β-causality t i q))) q j

Ω₀ : Schedule n → Γ₀-State → 𝕋 → Γ₀-State
Ω₀ ψ X t = Ω₀' ψ X (<-wellFounded t)
