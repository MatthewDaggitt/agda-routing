open import Data.Fin using (Fin; _≟_)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary using (Setoid; DecSetoid)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Relation.Binary.Indexed.Homogeneous
open import RoutingLib.Data.Matrix
import RoutingLib.Data.Matrix.Relation.DecidableEquality as MatrixDecEquality
import RoutingLib.Data.Table.Relation.DecidableEquality as TableDecEquality
open import RoutingLib.Data.Table using (Table)

open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.Model
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) (n : ℕ)
  where

open RawRoutingAlgebra algebra hiding (_≟_)

--------------------------------------------------------------------------------
-- Adjacency matrices represent the network topology

AdjacencyMatrix : Set a
AdjacencyMatrix = ∀ (i j : Fin n) → Step i j

--------------------------------------------------------------------------------
-- Routing tables store a node's routing decisions

RoutingTable : Set b
RoutingTable = Table Route n

-- Properties
open TableDecEquality DS public

ℝ𝕋ₛ : Setoid b ℓ
ℝ𝕋ₛ = 𝕋ₛ n

Decℝ𝕋ₛ : DecSetoid b ℓ
Decℝ𝕋ₛ = Dec𝕋ₛ n

ℝ𝕋ₛⁱ : IndexedSetoid (Fin n) _ _
ℝ𝕋ₛⁱ = triviallyIndexSetoid (Fin n) S

--------------------------------------------------------------------------------
-- Routing matrices store the routing decisions of the entire network

RoutingMatrix : Set b
RoutingMatrix = SquareMatrix Route n

-- Properties
open MatrixDecEquality DS public

ℝ𝕄ₛ : Setoid b ℓ
ℝ𝕄ₛ = 𝕄ₛ n n

ℝ𝕄ₛⁱ : IndexedSetoid (Fin n) _ _
ℝ𝕄ₛⁱ = triviallyIndexSetoid (Fin n) ℝ𝕋ₛ

Decℝ𝕄ₛ : DecSetoid b ℓ
Decℝ𝕄ₛ = Dec𝕄ₛ n n

Decℝ𝕄ₛⁱ : IndexedDecSetoid (Fin n) b ℓ
Decℝ𝕄ₛⁱ = triviallyIndexDecSetoid (Fin n) Decℝ𝕋ₛ

--------------------------------------------------------------------------------
-- The initial state (the identity matrix)

I : RoutingMatrix
I i j with j ≟ i
... | yes _ = 0#
... | no  _ = ∞

-- Properties
Iᵢⱼ≈0⊎∞ : ∀ i j → (I i j ≈ 0#) ⊎ (I i j ≈ ∞)
Iᵢⱼ≈0⊎∞ i j with j ≟ i
... | yes _ = inj₁ ≈-refl
... | no  _ = inj₂ ≈-refl

Iᵢᵢ≡0# : ∀ i → I i i ≡ 0#
Iᵢᵢ≡0# i with i ≟ i
... | yes _   = refl
... | no  i≢i = contradiction refl i≢i

Iᵢⱼ≡∞ : ∀ {i j} → j ≢ i → I i j ≡ ∞
Iᵢⱼ≡∞ {i} {j} i≢j with j ≟ i
... | yes i≡j = contradiction i≡j i≢j
... | no  _   = refl

Iᵢⱼ≡Iₖₗ : ∀ {i j k l} → j ≢ i → l ≢ k → I i j ≡ I k l
Iᵢⱼ≡Iₖₗ j≢i l≢k = trans (Iᵢⱼ≡∞ j≢i) (sym (Iᵢⱼ≡∞ l≢k))
