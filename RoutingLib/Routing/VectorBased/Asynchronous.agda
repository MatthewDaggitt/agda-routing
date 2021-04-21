--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module contains an asynchronous implementation of an abstract vector
-- based routing protocol designed to solve the routing problem described by the
-- provided routing algebra.
--------------------------------------------------------------------------------

open import Relation.Binary.Indexed.Homogeneous using (IndexedDecSetoid)

open import RoutingLib.Iteration.Asynchronous.Dynamic
  using (IsAsyncIterable; AsyncIterable; asyncIter)
open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule
  using (Schedule; 𝕋)

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Basics.Network using (Network)

module RoutingLib.Routing.VectorBased.Asynchronous
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n} (N : Network algebra n)
  where

open RawRoutingAlgebra algebra

------------------------------------------------------------------------
-- Publicly re-export core iteration and contents of routing

open import RoutingLib.Routing.Prelude algebra n public
  hiding (Network)

open import RoutingLib.Routing.Basics.Network.Participants algebra N public
  using (Aₜ)
  
open import RoutingLib.Routing.VectorBased.Synchronous algebra public
  using (F; σ; F-cong)
  
------------------------------------------------------------------------
-- The iteration being computed during epoch e with participants p

F′ : Epoch → Participants → RoutingMatrix → RoutingMatrix
F′ e p X = F (Aₜ e p) X

F′-cong : ∀ e p {X Y} → X ≈ₘ Y → F′ e p X ≈ₘ[ p ] F′ e p Y
F′-cong e p X≈Y {i} _ j = F-cong (Aₜ e p) X≈Y i j

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

