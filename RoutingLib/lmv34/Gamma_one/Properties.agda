open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary using (Rel)
import Relation.Binary.EqReasoning as EqReasoning

open import RoutingLib.lmv34.Function using (_^_)
open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra)
open import RoutingLib.Routing as Routing using (AdjacencyMatrix)
import RoutingLib.lmv34.Gamma_zero as Gamma_zero
import RoutingLib.lmv34.Gamma_zero.Algebra as Gamma_zero_Algebra
import RoutingLib.lmv34.Gamma_one as Gamma_one
import RoutingLib.lmv34.Gamma_one.Algebra as Gamma_one_Algebra

module RoutingLib.lmv34.Gamma_one.Properties
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n} (A : AdjacencyMatrix algebra n)
  where

open Routing algebra n
open Gamma_zero algebra A
open Gamma_zero_Algebra algebra n
open Gamma_one algebra A
open Gamma_one_Algebra algebra n

infix 4 _≈ᵥ_
_≈ᵥ_ : Rel RoutingVector ℓ
_≈ᵥ_ = {!!}

-- Theorem 2
FixedPoint-Γ₁ : {X : RoutingMatrix} →
                (X ≈ₘ (A 〔 X 〕 ⊕ₘ I)) →
                ~ X ≈ᵥ (A 〚 ~ X 〛 ⊕ᵥ ~ I)
FixedPoint-Γ₁ {X} = {!!}

-- Theorem 3
Γ₀=Γ₁ : {Y : RoutingMatrix} →
        Γ₁ (~ Y) ≈ᵥ ~ (Γ₀ Y)
Γ₀=Γ₁ {Y} = {!!}

-- Theorem 4
Γ₀=Γ₁-k : ∀ {k} {Y : RoutingMatrix} →
        (Γ₁ ^ k) (~ Y) ≈ᵥ ~ ((Γ₀ ^ k) Y) 
Γ₀=Γ₁-k {zero} {Y} = {!!}
Γ₀=Γ₁-k {suc k} {Y} = {!!}
