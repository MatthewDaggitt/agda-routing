open import Data.Nat using (ℕ; zero; suc)
import Relation.Binary.EqReasoning as EqReasoning

open import RoutingLib.lmv34.Function using (_^_)
open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra)
open import RoutingLib.Routing as Routing using (AdjacencyMatrix)
import RoutingLib.lmv34.Gamma_zero as Gamma_zero
import RoutingLib.lmv34.Gamma_zero.Algebra as Gamma_zero_Algebra

module RoutingLib.lmv34.Gamma_zero.Properties
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n} (A : AdjacencyMatrix algebra n)
  where

open Routing algebra n
open Gamma_zero algebra A
open Gamma_zero_Algebra algebra n

-- Theorem 1
FixedPoint-Γ₀ : ∀ {k} → {Y : RoutingMatrix} →
                ((Γ₀ ^ suc k) Y) ≈ₘ ((Γ₀ ^ k) Y) →
                (Γ₀ ^ k) Y ≈ₘ (A 〔 (Γ₀ ^ k) Y 〕 ⊕ₘ I)
FixedPoint-Γ₀ {k} {Y} p = begin
  (Γ₀ ^ k) Y              ≈⟨ ≈ₘ-sym p ⟩
  (Γ₀ ^ suc k) Y          ≈⟨ ≈ₘ-refl ⟩
  A 〔 (Γ₀ ^ k) Y 〕 ⊕ₘ I ∎
  where open EqReasoning (ℝ𝕄ₛ )
