{-# OPTIONS --allow-unsolved-metas #-}

open import Function using (const)
open import Relation.Binary.Indexed.Homogeneous using (IndexedDecSetoid)

open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra)
open import RoutingLib.Routing as Routing using (AdjacencyMatrix)
import RoutingLib.lmv34.Gamma_zero as Gamma_zero
import RoutingLib.lmv34.Gamma_zero.Properties as Gamma_zero_Properties
open import RoutingLib.Iteration.Asynchronous.Static using (AsyncIterable; asyncIter)
open import RoutingLib.Iteration.Asynchronous.Static.Schedule using (Schedule; 𝕋)

module RoutingLib.lmv34.Omega_zero
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n} (A : AdjacencyMatrix algebra n)
  where

open Routing algebra n using (RoutingTable; RoutingMatrix; Decℝ𝕄ₛⁱ; _≈ₜ_)
open Gamma_zero algebra A using (Γ₀)
open Gamma_zero_Properties algebra A using (Γ₀-cong)
open IndexedDecSetoid Decℝ𝕄ₛⁱ renaming (isDecEquivalenceᵢ to ℝ𝕄-isDecEquivalenceᵢ)

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
