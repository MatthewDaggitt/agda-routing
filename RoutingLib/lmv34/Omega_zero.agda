{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Subset using (Subset; ⊥; ⊤)
open import Function using (const)
open import Relation.Binary.Indexed.Homogeneous using (IndexedDecSetoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra)
open import RoutingLib.Routing as Routing using (AdjacencyMatrix)
import RoutingLib.lmv34.Gamma_zero as Gamma_zero
import RoutingLib.lmv34.Gamma_zero.Algebra as Gamma_zero_Algebra
import RoutingLib.lmv34.Gamma_zero.Properties as Gamma_zero_Properties
open import RoutingLib.Iteration.Asynchronous.Static using (AsyncIterable; asyncIter; asyncIter')
open import RoutingLib.Iteration.Asynchronous.Static.Schedule using (Schedule; 𝕋)
open import RoutingLib.Iteration.Asynchronous.Static.Schedule.Construct.Synchronous using (ψˢʸⁿᶜ; ψˢʸⁿᶜ-isSynchronous)
open import RoutingLib.Iteration.Synchronous using (_^_)

module RoutingLib.lmv34.Omega_zero
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n} (A : AdjacencyMatrix algebra n)
  where

open RawRoutingAlgebra algebra using (≈-refl; S)
open Routing algebra n using (RoutingTable; RoutingMatrix; Decℝ𝕄ₛⁱ; _≈ₘ_; _≈ₜ_)
open Gamma_zero algebra A using (Γ₀)
open Gamma_zero_Properties algebra A using (Γ₀-cong)
open IndexedDecSetoid Decℝ𝕄ₛⁱ renaming (isDecEquivalenceᵢ to ℝ𝕄-isDecEquivalenceᵢ)

------------------------------------
-- Definitions
------------------------------------

-- Asynchronous model

Γ₀∥ : AsyncIterable a ℓ n
Γ₀∥ = record {
  Sᵢ   = const RoutingTable;
  _≈ᵢ_ = _≈ₜ_;
  F    = Γ₀;
  isAsyncIterable = record {
    isDecEquivalenceᵢ = ℝ𝕄-isDecEquivalenceᵢ;
    F-cong = Γ₀-cong
    }
  }

Ω₀ : Schedule n → RoutingMatrix → 𝕋 → RoutingMatrix
Ω₀ ψ = asyncIter Γ₀∥ ψ

-- The infinitely asynchronous schedule
ψ∞ : ∀ {n} → Schedule n
ψ∞ {n} = record {α = α ; β = β ; β-causality = β-causality }
  where α : (t : 𝕋) → Subset n
        α t = ⊥
        
        β : (t : 𝕋) → (i j : Fin n) → 𝕋
        β t _ _ = zero
        
        β-causality : ∀ t i j → β (suc t) i j ≤ t
        β-causality t _ _ = z≤n

------------------------------------
-- Properties
------------------------------------

-- Γ₀ is indeed the synchronous version of Ω₀
Ω₀-sync=Γ₀ : ∀ X t → Ω₀ ψˢʸⁿᶜ X t ≈ₘ (Γ₀ ^ t) X
Ω₀-sync=Γ₀ = ψˢʸⁿᶜ-isSynchronous Γ₀∥
