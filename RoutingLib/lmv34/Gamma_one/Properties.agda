open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary using (Rel)
import Relation.Binary.EqReasoning as EqReasoning

open import RoutingLib.lmv34.Function using (_^_)
open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
open import RoutingLib.Routing as Routing using (AdjacencyMatrix)
import RoutingLib.lmv34.Gamma_zero as Gamma_zero
import RoutingLib.lmv34.Gamma_zero.Algebra as Gamma_zero_Algebra
import RoutingLib.lmv34.Gamma_one as Gamma_one
import RoutingLib.lmv34.Gamma_one.Algebra as Gamma_one_Algebra

module RoutingLib.lmv34.Gamma_one.Properties
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  {n} (A : AdjacencyMatrix algebra n)
  where

open Routing algebra n
open Gamma_zero algebra A
open Gamma_zero_Algebra algebra n
open Gamma_one isRoutingAlgebra A
open Gamma_one_Algebra isRoutingAlgebra n

-- Theorem 3
Γ₀=Γ₁ : {Y : RoutingMatrix} →
        Γ₁ (~ Y) ≈ᵥ ~ (Γ₀ Y)
Γ₀=Γ₁ {Y} = {!!}

-- Theorem 2
FixedPoint-Γ₁ : {X : RoutingMatrix} →
                (X ≈ₘ (A 〔 X 〕 ⊕ₘ I)) →
                ~ X ≈ᵥ (A 〚 ~ X 〛 ⊕ᵥ ~ I)
FixedPoint-Γ₁ {X} p = begin
  ~ X                 ≈ᵥ⟨ {!!} ⟩
  ~ (A 〔 X 〕 ⊕ₘ I)  ≈ᵥ⟨ {!!} ⟩
  ~ (Γ₀ X)            ≈ᵥ⟨ ≈ᵥ-sym Γ₀=Γ₁ ⟩
  Γ₁ (~ X)            ≈ᵥ⟨ ≈ᵥ-refl ⟩
  A 〚 ~ X 〛 ⊕ᵥ ~ I  ∎

-- Theorem 4
Γ₀=Γ₁-iter : ∀ {k} {Y : RoutingMatrix} →
        (Γ₁ ^ k) (~ Y) ≈ᵥ ~ ((Γ₀ ^ k) Y) 
Γ₀=Γ₁-iter {zero} {Y} = ≈ᵥ-refl
Γ₀=Γ₁-iter {suc k} {Y} = begin
  (Γ₁ ^ suc k) (~ Y)  ≈ᵥ⟨ ≈ᵥ-refl ⟩
  Γ₁ ((Γ₁ ^ k) (~ Y)) ≈ᵥ⟨ {!!} ⟩
  Γ₁ (~ ((Γ₀ ^ k) Y)) ≈ᵥ⟨ Γ₀=Γ₁ ⟩
  ~ (Γ₀ ((Γ₀ ^ k) Y)) ≈ᵥ⟨ ≈ᵥ-refl ⟩
  ~ (Γ₀ ^ suc k) Y    ∎
