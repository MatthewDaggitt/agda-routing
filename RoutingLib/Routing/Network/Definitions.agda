--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module contains the basic definitions needed for all next-hop routing
-- routing algorithms. This contains the definition of things like the network,
-- the adjacency matrix, routing tables, global routing state etc.
--------------------------------------------------------------------------------

open import Data.Fin using (Fin) renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Subset using (Subset; _∉_)
open import Data.Fin.Properties using (any?)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃₂; _×_; _,_)
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)
import Relation.Binary.Reasoning.Setoid as EqReasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Routing.Algebra
import RoutingLib.Routing as Routing

module RoutingLib.Routing.Network.Definitions
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n} (open Routing algebra n)
  (N : Network)
  where

open RawRoutingAlgebra algebra
open import RoutingLib.Routing.AdjacencyMatrix.Cycles algebra

------------------------------------------------------------------------
-- The adjacency matrix in each epoch, adjusted for participants

Aₜ : Epoch → Subset n → AdjacencyMatrix
Aₜ e p i j with i ∈? p | j ∈? p
... | yes _ | yes _ = N e i j
... | _     | _     = f∞ i j

------------------------------------------------------------------------
-- Free networks

-- A network is free during an epoch and set of participants if the
-- resulting participation topology is CycleFree

TopologyIsFree : Epoch × Subset n → Set (a ⊔ ℓ)
TopologyIsFree (e , p) = CycleFree (Aₜ e p)
