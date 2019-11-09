--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module contains the basic definitions needed for all next-hop routing
-- routing algorithms. This contains the definition of things like the network,
-- the adjacency matrix, routing tables, global routing state etc.
--------------------------------------------------------------------------------

open import RoutingLib.Routing.Algebra
open import Data.Nat using (ℕ)

module RoutingLib.Routing.Network
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
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
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Routing algebra as Routing using (AdjacencyMatrix; CycleFree)

open RawRoutingAlgebra algebra

--------------------------------------------------------------------------------
-- A network is a epoch indexed family of adjacency matrices

open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule public
  using (Epoch)

-- TODO make Network a record and hide the size

Network : ℕ → Set b
Network n = Epoch → AdjacencyMatrix n

------------------------------------------------------------------------
-- The adjacency matrix in each epoch, adjusted for participants

module _ {n} (network : Network n) where

  open Routing n hiding (AdjacencyMatrix)
  
  Aₜ : Epoch → Subset n → AdjacencyMatrix n
  Aₜ e p i j with i ∈? p | j ∈? p
  ... | yes _ | yes _ = network e i j
  ... | _     | _     = f∞ i j

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
  ... | yes _ | yes k∈p = ▷-cong (network e i k) (X≈Y k∈p j)
  ... | yes _ | no  _   = ≈-trans (f∞-reject i k (X k j)) (≈-sym (f∞-reject i k (Y k j)))
  ... | no  _ | yes _   = ≈-trans (f∞-reject i k (X k j)) (≈-sym (f∞-reject i k (Y k j)))
  ... | no  _ | no  _   = ≈-trans (f∞-reject i k (X k j)) (≈-sym (f∞-reject i k (Y k j)))


------------------------------------------------------------------------
-- Free networks

-- A network is free if for any epoch and set of participants, then it's
-- topology remains CycleFree

IsFree : ∀ {n} → Network n → Set (a ⊔ ℓ)
IsFree N = ∀ e p → CycleFree _ (Aₜ N e p)
