--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module contains an asynchronous implementation of an abstract vector
-- based routing protocol designed to solve the routing problem described by the
-- provided routing algebra.
--------------------------------------------------------------------------------

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing as Routing using (Network)

module RoutingLib.Routing.VectorBased.Asynchronous
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n} (network : Network algebra n)
  where

open import Data.List.Relation.Binary.Pointwise using (tabulate⁺)
open import Data.Fin.Subset using (Subset; _∉_)
open import Relation.Binary.Indexed.Homogeneous using (IndexedDecSetoid)

open import RoutingLib.Data.List.Relation.Binary.Pointwise using (foldr⁺)

open import RoutingLib.Iteration.Asynchronous.Dynamic
  using (IsAsyncIterable; AsyncIterable; asyncIter)
open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule
  using (Schedule; 𝕋)
import RoutingLib.Routing.VectorBased.Synchronous as Synchronous

open RawRoutingAlgebra algebra

------------------------------------------------------------------------
-- Publicly re-export core iteration and contents of routing

open Synchronous algebra public
  using (F; σ; F-cong)
open Routing algebra n public
  hiding (Aₜ)

------------------------------------------------------------------------
-- The adjacency matrix at time e with participants p

Aₜ : Epoch → Subset n → AdjacencyMatrix
Aₜ = Routing.Aₜ algebra n network

------------------------------------------------------------------------
-- The iteration being computed during epoch e with participants p

F′ : Epoch → Subset n → RoutingMatrix → RoutingMatrix
F′ e p X = F (Aₜ e p) X

F′-cong : ∀ e p {X Y} → X ≈ₘ Y → F′ e p X ≈ₘ[ p ] F′ e p Y
F′-cong e p X≈Y _ j = foldr⁺ _≈_ ⊕-cong ≈-refl (tabulate⁺ (Aₜ-cong _ e p (λ _ → X≈Y _)))

F′-isAsyncIterable : IsAsyncIterable _≈ₜ_ F′ I
F′-isAsyncIterable = record
  { isDecEquivalenceᵢ = IndexedDecSetoid.isDecEquivalenceᵢ Decℝ𝕄ₛⁱ
  ; F-cong            = F′-cong
  }

F∥ : AsyncIterable a ℓ n
F∥ = record
  { isAsyncIterable = F′-isAsyncIterable
  }

------------------------------------------------------------------------
-- The asynchronous state function
--
-- Given a schedule "ψ" and an initial state "X" then "δ ψ X t" is
-- the resulting state at time "t"

δ : Schedule n → RoutingMatrix → 𝕋 → RoutingMatrix
δ = asyncIter F∥
