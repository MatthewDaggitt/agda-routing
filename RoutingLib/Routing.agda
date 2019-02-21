open import Data.Fin using (Fin) renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Subset using (Subset; _∉_)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary using (Setoid; DecSetoid)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)
open import Relation.Binary.Indexed.Homogeneous using (IndexedSetoid; IndexedDecSetoid)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Relation.Binary.Indexed.Homogeneous
import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.FiniteSubset.Equality as SubsetEquality
open import RoutingLib.Data.Matrix
import RoutingLib.Data.Matrix.Relation.DecidableEquality as MatrixDecEquality
import RoutingLib.Data.Table.Relation.DecidableEquality as TableDecEquality
open import RoutingLib.Data.Table using (Table)

open import RoutingLib.Routing.Algebra
import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule as Schedule

module RoutingLib.Routing
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) (n : ℕ)
  where

open RawRoutingAlgebra algebra

--------------------------------------------------------------------------------
-- Publicly re-export the concept of an epoch

open Schedule public using (Epoch)

--------------------------------------------------------------------------------
-- Adjacency matrices represent the topology of the network at a point in time

AdjacencyMatrix : Set b
AdjacencyMatrix = ∀ (i j : Fin n) → Step i j

--------------------------------------------------------------------------------
-- A network is a epoch indexed family of adjacency matrices

Network : Set b
Network = Epoch → AdjacencyMatrix

--------------------------------------------------------------------------------
-- Routing tables store a node's routing decisions

RoutingTable : Set a
RoutingTable = Table Route n

-- Properties
open TableDecEquality DS public

ℝ𝕋ₛ : Setoid a ℓ
ℝ𝕋ₛ = 𝕋ₛ n

Decℝ𝕋ₛ : DecSetoid a ℓ
Decℝ𝕋ₛ = Dec𝕋ₛ n

ℝ𝕋ₛⁱ : IndexedSetoid (Fin n) _ _
ℝ𝕋ₛⁱ = triviallyIndexSetoid (Fin n) S

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
... | no  _ = ∞

-- Properties
Iᵢⱼ≈0⊎∞ : ∀ i j → (I i j ≈ 0#) ⊎ (I i j ≈ ∞)
Iᵢⱼ≈0⊎∞ i j with j ≟𝔽 i
... | yes _ = inj₁ ≈-refl
... | no  _ = inj₂ ≈-refl

Iᵢᵢ≡0# : ∀ i → I i i ≡ 0#
Iᵢᵢ≡0# i with i ≟𝔽 i
... | yes _   = refl
... | no  i≢i = contradiction refl i≢i

Iᵢⱼ≡∞ : ∀ {i j} → j ≢ i → I i j ≡ ∞
Iᵢⱼ≡∞ {i} {j} i≢j with j ≟𝔽 i
... | yes i≡j = contradiction i≡j i≢j
... | no  _   = refl

Iᵢⱼ≡Iₖₗ : ∀ {i j k l} → j ≢ i → l ≢ k → I i j ≡ I k l
Iᵢⱼ≡Iₖₗ j≢i l≢k = trans (Iᵢⱼ≡∞ j≢i) (sym (Iᵢⱼ≡∞ l≢k))

------------------------------------------------------------------------
-- The adjacency matrix in each epoch, adjusted for participants

module _ (network : Network) where

  -- abstract

    -- Needs to be abstract otherwise unfolding causes all sorts of problems

    Aₜ : Epoch → Subset n → AdjacencyMatrix
    Aₜ e p i j with i ∈? p | j ∈? p
    ... | yes _ | yes _ = network e i j
    ... | _     | _     = f∞ i j

    Aₜ-reject : ∀ e {p} i j → i ∉ p ⊎ j ∉ p → ∀ x → Aₜ e p i j ▷ x ≈ ∞
    Aₜ-reject e {p} i j op x with i ∈? p | j ∈? p
    ... | yes _   | no  _   = f∞-reject i j x
    ... | no  _   | yes _   = f∞-reject i j x
    ... | no  _   | no  _   = f∞-reject i j x
    ... | yes i∈p | yes j∈p with op
    ...   | inj₁ i∉p = contradiction i∈p i∉p
    ...   | inj₂ j∉p = contradiction j∈p j∉p

    Aₜ-reject-eq : ∀ e {p} i j → i ∉ p → ∀ x y → Aₜ e p i j ▷ x ≈ Aₜ e p i j ▷ y
    Aₜ-reject-eq e {p} i j i∉p x y = begin
      Aₜ e p i j ▷ x ≈⟨ Aₜ-reject e i j (inj₁ i∉p) x ⟩
      ∞              ≈⟨ ≈-sym (Aₜ-reject e i j (inj₁ i∉p) y) ⟩
      Aₜ e p i j ▷ y ∎
      where open EqReasoning S

    Aₜ-cong : ∀ e p {X Y : RoutingMatrix} → X ≈ₘ[ p ] Y →
              ∀ {i j} k → Aₜ e p i k ▷ X k j ≈ Aₜ e p i k ▷ Y k j
    Aₜ-cong e p {X} {Y} X≈Y {i} {j} k with i ∈? p | k ∈? p
    ... | yes _ | yes k∈p = ▷-cong (network e i k) (X≈Y k∈p j)
    ... | yes _ | no  _   = ≈-trans (f∞-reject i k (X k j)) (≈-sym (f∞-reject i k (Y k j)))
    ... | no  _ | yes _   = ≈-trans (f∞-reject i k (X k j)) (≈-sym (f∞-reject i k (Y k j)))
    ... | no  _ | no  _   = ≈-trans (f∞-reject i k (X k j)) (≈-sym (f∞-reject i k (Y k j)))

--------------------------------------------------------------------------------
-- WellFormed

-- Let p be the set of active nodes, then a routing matrix is well-formed if
-- every entry not in the subset is inactive

WellFormed : Subset n → RoutingMatrix → Set ℓ
WellFormed p X = ∀ {i} → i ∉ p → X i ≈ₜ I i

WellFormed-cong : ∀ {X Y p} → WellFormed p X → WellFormed p Y →
                  ∀ {i} → i ∉ p → X i ≈ₜ Y i
WellFormed-cong wfX wfY i∉p = ≈ₜ-trans (wfX i∉p) (≈ₜ-sym (wfY i∉p))
