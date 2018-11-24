open import Data.Nat using (ℕ)
open import Data.List using (foldr; tabulate)
open import Data.List.Relation.Pointwise using (tabulate⁺)

open import RoutingLib.Data.List.Relation.Pointwise using (foldr⁺)
open import RoutingLib.Iteration.Synchronous

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing as Routing using (AdjacencyMatrix)
import RoutingLib.Routing.VectorBased.Core as Core

module RoutingLib.Routing.VectorBased.Synchronous
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n} (A : AdjacencyMatrix algebra n)
  where

--------------------------------------------------------------------------------
-- Publicly re-export core iteration and contents of routing

open Routing algebra n public
open Core algebra A public

--------------------------------------------------------------------------------
-- Synchronous state function

σ : ℕ → RoutingMatrix → RoutingMatrix
σ = F ^_
