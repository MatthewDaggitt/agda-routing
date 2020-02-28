--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module contains the basic definitions needed for all next-hop routing
-- routing algorithms. This contains the definition of things like the network,
-- the adjacency matrix, routing tables, global routing state etc.
--------------------------------------------------------------------------------

open import RoutingLib.Routing.Algebra
import RoutingLib.Routing as Routing

module RoutingLib.Routing.Network.Properties
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n} (open Routing algebra n)
  (N : Network)
  where

open import Data.Fin using (Fin) renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Subset using (Subset; _∉_)
open import Data.Fin.Properties using (any?)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃₂)
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)
import Relation.Binary.Reasoning.Setoid as EqReasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import RoutingLib.Data.Fin using (_+ₘ_; _-ₘ_)
open import RoutingLib.Data.FiniteSet using (⟦_∣_⟧) renaming (FiniteSet to FiniteSet⁺)

open RawRoutingAlgebra algebra

open import RoutingLib.Routing.Network.Definitions algebra N
import RoutingLib.Routing.AdjacencyMatrix.Cycles as Cycles

------------------------------------------------------------------------
-- The adjacency matrix in each epoch, adjusted for participants

Aₜ-reject : ∀ e {p} i j → i ∉ p ⊎ j ∉ p → ∀ x → Aₜ e p i j ▷ x ≈ ∞#
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
  ∞#             ≈⟨ ≈-sym (Aₜ-reject e i j (inj₁ i∉p) y) ⟩
  Aₜ e p i j ▷ y ∎
  where open EqReasoning S

Aₜ-cong : ∀ e p {X Y : RoutingMatrix} → X ≈ₘ[ p ] Y →
          ∀ {i j} k → Aₜ e p i k ▷ X k j ≈ Aₜ e p i k ▷ Y k j
Aₜ-cong e p {X} {Y} X≈Y {i} {j} k with i ∈? p | k ∈? p
... | yes _ | yes k∈p = ▷-cong (N e i k) (X≈Y k∈p j)
... | yes _ | no  _   = ≈-trans (f∞-reject i k (X k j)) (≈-sym (f∞-reject i k (Y k j)))
... | no  _ | yes _   = ≈-trans (f∞-reject i k (X k j)) (≈-sym (f∞-reject i k (Y k j)))
... | no  _ | no  _   = ≈-trans (f∞-reject i k (X k j)) (≈-sym (f∞-reject i k (Y k j)))

------------------------------------------------------------------------
-- Free networks

-- If the algebra is strictly increasing, then every network is free
strIncr⇒free : IsRoutingAlgebra algebra → IsStrictlyIncreasing algebra → Free
strIncr⇒free isRoutingAlg strIncr N p = Cycles.strIncr⇒allCycleFree _ isRoutingAlg strIncr (Aₜ N p)
