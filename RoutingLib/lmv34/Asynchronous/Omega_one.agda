open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
open import RoutingLib.Routing as Routing using () renaming (AdjacencyMatrix to AdjacencyMatrix')

module RoutingLib.lmv34.Asynchronous.Omega_one
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  {n} (A : AdjacencyMatrix' algebra n)
  where

open import Data.Fin using (Fin)
open import Data.Nat using (zero; suc; s≤s; _<_)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Data.Nat.Properties using (≤-refl)
open import Function using (id)

open import RoutingLib.Iteration.Asynchronous.Static.Schedule using (Schedule; 𝕋)
open import RoutingLib.lmv34.Asynchronous.Omega_zero.Algebra algebra A using ([_,_]_)
open import RoutingLib.lmv34.Asynchronous.Omega_one.Algebra isRoutingAlgebra A using (Γ₁')
open import RoutingLib.lmv34.Synchronous.Gamma_zero algebra A
open import RoutingLib.lmv34.Synchronous.Gamma_one isRoutingAlgebra A
open import RoutingLib.lmv34.Synchronous.Gamma_one.Algebra isRoutingAlgebra n using (RoutingVector; ─_)

open Routing algebra n using (RoutingMatrix)

--------------------------------------------------------------------------------
-- Implementation of Ω₁

module _ (ψ : Schedule n) where
  open Schedule ψ
  
  Ω₁' : Γ₁-State → {t : 𝕋} → Acc _<_ t → Γ₁-State
  Ω₁' V {zero}  _         = V
  Ω₁' V {suc t} (acc rec) = [ Γ₁' V[β[t+1]] , V[t] ] α (suc t)
    where V[t] : RoutingVector
          V[t] = Ω₁' V (rec t ≤-refl)
          V[β[t+1]] : Fin n → RoutingVector
          V[β[t+1]] i q = Ω₁' V (rec (β (suc t) i q) (s≤s (β-causality t i q))) q

Ω₁ : Schedule n → Γ₁-State → 𝕋 → Γ₁-State
Ω₁ ψ V t = Ω₁' ψ V (<-wellFounded t)

--------------------------------------------------------------------------------
-- Reduction/transformation Ω₁ → Ω₀

-- Transformation Ω₁ → Ω₀
Τ₁ : Γ₁-State → Γ₀-State
Τ₁ V = ─ V

-- Schedule reduction Ω₁ → Ω₀
r₁ : ∀ {n} → Schedule n → Schedule n
r₁ = id
