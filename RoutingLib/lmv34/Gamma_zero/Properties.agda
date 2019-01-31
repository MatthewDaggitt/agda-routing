open import Data.Nat using (ℕ; zero; suc)
open import Function using (id; _∘_)
import Relation.Binary.EqReasoning as EqReasoning

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

infix 20 _^_
_^_ : ∀ {a} {A : Set a} → (A → A) → ℕ → A → A
f ^ zero = id
f ^ (suc n) = f ∘ (f ^ n)

-- Theorem 1
FixedPoint-Γ₀ : ∀ {k} → {Y : RoutingMatrix} →
                ((Γ₀ ^ suc k) Y) ≈ₘ ((Γ₀ ^ k) Y) →
                (Γ₀ ^ k) Y ≈ₘ (A 〚 (Γ₀ ^ k) Y 〛 M⊕ I)
FixedPoint-Γ₀ {k} {Y} p = begin
  (Γ₀ ^ k) Y              ≈⟨ ≈ₘ-sym p ⟩
  (Γ₀ ^ suc k) Y          ≈⟨ ≈ₘ-refl ⟩
  A 〚 (Γ₀ ^ k) Y 〛 M⊕ I ∎
  where open EqReasoning (ℝ𝕄ₛ )
