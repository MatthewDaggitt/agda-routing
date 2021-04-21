--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module contains a synchronous implementation of an abstract vector
-- based routing protocol designed to solve the routing problem described by the
-- provided routing algebra.
--------------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (foldr; tabulate)
open import Data.List.Relation.Binary.Pointwise using (tabulate⁺; foldr⁺)

open import RoutingLib.Iteration.Synchronous
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Basics.Network using (AdjacencyMatrix)

module RoutingLib.Routing.VectorBased.Synchronous
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n : ℕ} (A : AdjacencyMatrix algebra n)
  where

open RawRoutingAlgebra algebra

--------------------------------------------------------------------------------
-- Publicly re-export the contents of the routing prelude so that we don't have
-- to open every time we used vector-based routing.

open import RoutingLib.Routing.Prelude algebra n public

--------------------------------------------------------------------------------
-- Algorithm

-- A single iteration
F : RoutingMatrix → RoutingMatrix
F X i j = foldr _⊕_ (I i j) (tabulate (λ k → A i k ▷ X k j))

-- Multiple iterations
σ : ℕ → RoutingMatrix → RoutingMatrix
σ = F ^_

-- F respects the underlying matrix equality
F-cong : ∀ {X Y} → X ≈ₘ Y → F X ≈ₘ F Y
F-cong X≈Y i j = foldr⁺ {R = _≈_} ⊕-cong ≈-refl (tabulate⁺ (λ k → ▷-cong _ (X≈Y k j)))

-- σ respects the underlying matrix equality
σ-cong : ∀ t {X Y} → X ≈ₘ Y → σ t X ≈ₘ σ t Y
σ-cong zero    X≈Y = X≈Y
σ-cong (suc t) X≈Y = F-cong (σ-cong t X≈Y)
