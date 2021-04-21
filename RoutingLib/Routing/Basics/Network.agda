--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module contains the basic definitions needed for all next-hop routing
-- routing algorithms. This contains the definition of things like the network,
-- the adjacency matrix, routing tables, global routing state etc.
--------------------------------------------------------------------------------

open import Data.Fin.Subset using (Subset; _∉_)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; _×_)
open import Data.Nat using (ℕ)
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule using (Epoch)
  
open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.Basics.Network
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  (n : ℕ)
  where

open RawRoutingAlgebra algebra
open import RoutingLib.Routing.Basics.Node n

------------------------------------------------------------------------
-- Definition

AdjacencyMatrix : Set b
AdjacencyMatrix = ∀ (i j : Node) → Step i j

-- A network is a epoch-indexed family of adjacency matrices

Network : Set b
Network = Epoch → AdjacencyMatrix
