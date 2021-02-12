--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module contains the basic definitions needed for all next-hop routing
-- routing algorithms. This contains the definition of things like the adjacency
-- matrix, routing tables, global routing state etc.
--------------------------------------------------------------------------------

open import RoutingLib.Routing.Algebra
open import Data.Nat using (ℕ)

module RoutingLib.Routing
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) (n : ℕ)
  where

open import Data.Fin using (Fin) renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Subset using (Subset; _∉_)
open import Data.Fin.Properties using (any?)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃₂)
open import Data.Vec.Functional using (Vector)
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)
open import Relation.Binary.Indexed.Homogeneous
  using (IndexedSetoid; IndexedDecSetoid)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Relation.Binary.Indexed.Homogeneous
import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.FiniteSubset.Equality as SubsetEquality
open import RoutingLib.Data.Matrix
import RoutingLib.Data.Matrix.Relation.Binary.DecidableEquality as MatrixDecEquality
import RoutingLib.Data.Vec.Functional.Relation.Binary.DecidableEquality as VectorDecEquality

import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule as Schedule

open RawRoutingAlgebra algebra

--------------------------------------------------------------------------------
-- Adjacency matrices represent the topology of the network at a point in time

AdjacencyMatrix : Set b
AdjacencyMatrix = ∀ (i j : Fin n) → Step i j

--------------------------------------------------------------------------------
-- A network is a epoch indexed family of adjacency matrices

open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule public
  using (Epoch)

-- TODO make Network a record and hide the size

Network : Set b
Network = Epoch → AdjacencyMatrix

--------------------------------------------------------------------------------
-- Routing tables store a node's routing decisions

RoutingTable : Set a
RoutingTable = Vector Route n

-- Properties
open VectorDecEquality DS public
  renaming
  ( _≋_     to _≈ₜ_
  ; ≋-refl  to ≈ₜ-refl
  ; ≋-sym   to ≈ₜ-sym
  ; ≋-trans to ≈ₜ-trans
  )

ℝ𝕋ₛ : Setoid a ℓ
ℝ𝕋ₛ = VectorDecEquality.≋-setoid DS n

Decℝ𝕋ₛ : DecSetoid a ℓ
Decℝ𝕋ₛ = VectorDecEquality.≋-decSetoid DS n

ℝ𝕋ₛⁱ : IndexedSetoid (Fin n) _ _
ℝ𝕋ₛⁱ = triviallyIndexSetoid (Fin n) S

Decℝ𝕋ₛⁱ : IndexedDecSetoid (Fin n) _ _
Decℝ𝕋ₛⁱ = triviallyIndexDecSetoid (Fin n) DS

--------------------------------------------------------------------------------
-- Routing matrices store the routing decisions of the entire network

RoutingMatrix : Set a
RoutingMatrix = SquareMatrix Route n

-- Standard equality
open MatrixDecEquality DS public

ℝ𝕄ₛ : Setoid a ℓ
ℝ𝕄ₛ = 𝕄ₛ n n

ℝ𝕄ₛⁱ : IndexedSetoid (Fin n) _ _
ℝ𝕄ₛⁱ = triviallyIndexSetoid (Fin n) ℝ𝕋ₛ

Decℝ𝕄ₛ : DecSetoid a ℓ
Decℝ𝕄ₛ = Dec𝕄ₛ n n

Decℝ𝕄ₛⁱ : IndexedDecSetoid (Fin n) a ℓ
Decℝ𝕄ₛⁱ = triviallyIndexDecSetoid (Fin n) Decℝ𝕋ₛ

-- Equality over only a subset of routing tables
open SubsetEquality ℝ𝕄ₛⁱ public
  using (≈ₛ-refl; ≈ₛ-sym; ≈ₛ-trans)
  renaming (_≈[_]_ to _≈ₘ[_]_; _≉[_]_ to _≉ₘ[_]_; ≈ₛ-setoid to ℝ𝕄ₛₛ)

--------------------------------------------------------------------------------
-- The initial state (the identity matrix)
--
-- In the initial state everyone knows the trivial route to themselves and has
-- an invalid route for everyone else

I : RoutingMatrix
I i j with j ≟𝔽 i
... | yes _ = 0#
... | no  _ = ∞#

-- Properties
Iᵢⱼ≈0⊎∞ : ∀ i j → (I i j ≈ 0#) ⊎ (I i j ≈ ∞#)
Iᵢⱼ≈0⊎∞ i j with j ≟𝔽 i
... | yes _ = inj₁ ≈-refl
... | no  _ = inj₂ ≈-refl

Iᵢᵢ≡0# : ∀ i → I i i ≡ 0#
Iᵢᵢ≡0# i with i ≟𝔽 i
... | yes _   = refl
... | no  i≢i = contradiction refl i≢i

Iᵢⱼ≡∞ : ∀ {i j} → j ≢ i → I i j ≡ ∞#
Iᵢⱼ≡∞ {i} {j} i≢j with j ≟𝔽 i
... | yes i≡j = contradiction i≡j i≢j
... | no  _   = refl

Iᵢⱼ≡Iₖₗ : ∀ {i j k l} → j ≢ i → l ≢ k → I i j ≡ I k l
Iᵢⱼ≡Iₖₗ j≢i l≢k = trans (Iᵢⱼ≡∞ j≢i) (sym (Iᵢⱼ≡∞ l≢k))

--------------------------------------------------------------------------------
-- WellFormed

-- Let p be the set of active nodes, then a routing matrix is well-formed if
-- every entry not in the subset is inactive

WellFormed : Subset n → RoutingMatrix → Set ℓ
WellFormed p X = ∀ {i} → i ∉ p → X i ≈ₜ I i

WellFormed-cong : ∀ {X Y p} → WellFormed p X → WellFormed p Y →
                  ∀ {i} → i ∉ p → X i ≈ₜ Y i
WellFormed-cong wfX wfY i∉p = ≈ₜ-trans (wfX i∉p) (≈ₜ-sym (wfY i∉p))
