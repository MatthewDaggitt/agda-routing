open import Data.List.Relation.Pointwise using (tabulate⁺)
open import Data.Fin using () renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Dec using (_∈?_)
open import Data.Fin.Subset using (Subset; _∉_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Indexed.Homogeneous using (IndexedDecSetoid)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

import RoutingLib.Data.Table.Relation.DecidableEquality as TableDecEquality
import RoutingLib.Data.Matrix.Relation.DecidableEquality as MatrixDecEquality
import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.FiniteSubset.Equality as SubsetEquality
open import RoutingLib.Data.List.Relation.Pointwise using (foldr⁺)
open import RoutingLib.Data.List

open import RoutingLib.Iteration.Asynchronous.Dynamic
open import RoutingLib.Iteration.Asynchronous.Schedule using (Schedule; 𝕋; Epoch)
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Model as Model using (Network)
import RoutingLib.Routing.BellmanFord.Synchronous as SynchronousBellmanFord

module RoutingLib.Routing.BellmanFord.Asynchronous
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n} (network : Network algebra n)
  where

open RawRoutingAlgebra algebra
open SynchronousBellmanFord algebra using (σ; σ-cong)

open Model algebra n public

------------------------------------------------------------------------
-- The adjacency matrix in each epoch, adjusted for participants

abstract
-- Needs to be abstract otherwise unfolding causes all sorts of problems

  Aₜ : Epoch → Subset n → AdjacencyMatrix
  Aₜ e p i j with i ∈? p | j ∈? p 
  ... | yes _ | yes _ = network e i j
  ... | _     | _     = f∞ i j

  Aₜ-cong : ∀ e p {X Y : RoutingMatrix} → X ≈ₘ[ p ] Y →
            ∀ {i j} k → Aₜ e p i k ▷ X k j ≈ Aₜ e p i k ▷ Y k j
  Aₜ-cong e p {X} {Y} X≈Y {i} {j} k with i ∈? p | k ∈? p
  ... | yes _ | yes k∈p = ▷-cong (network e i k) (X≈Y k∈p j)
  ... | yes _ | no  _   = ≈-trans (f∞-reject i k (X k j)) (≈-sym (f∞-reject i k (Y k j)))
  ... | no  _ | yes _   = ≈-trans (f∞-reject i k (X k j)) (≈-sym (f∞-reject i k (Y k j)))
  ... | no  _ | no  _   = ≈-trans (f∞-reject i k (X k j)) (≈-sym (f∞-reject i k (Y k j)))

  Aₜ-reject : ∀ e {p} i j → i ∉ p ⊎ j ∉ p → ∀ x → Aₜ e p i j ▷ x ≈ ∞
  Aₜ-reject e {p} i j op x with i ∈? p | j ∈? p
  ... | yes _   | no  _   = f∞-reject i j x
  ... | no  _   | yes _   = f∞-reject i j x
  ... | no  _   | no  _   = f∞-reject i j x
  ... | yes i∈p | yes j∈p with op
  ...   | inj₁ i∉p = contradiction i∈p i∉p
  ...   | inj₂ j∉p = contradiction j∈p j∉p

  Aₜ-reject-eq : ∀ e {p} i j → i ∉ p → ∀ x y → Aₜ e p i j ▷ x ≈ Aₜ e p i j ▷ y
  Aₜ-reject-eq e i j i∉p x y = ≈-trans (Aₜ-reject e i j (inj₁ i∉p) x) (≈-sym (Aₜ-reject e i j (inj₁ i∉p) y))

------------------------------------------------------------------------
-- The synchronous routing iteration being computed during epoch e
-- with participanets p

σₜ : Epoch → Subset n → RoutingMatrix → RoutingMatrix
σₜ e p X = σ (Aₜ e p) X

σₜ-cong : ∀ e p {X Y} → X ≈ₘ[ p ] Y → σₜ e p X ≈ₘ[ p ] σₜ e p Y
σₜ-cong e p X≈Y _ j = foldr⁺ _≈_ ⊕-cong ≈-refl (tabulate⁺ (Aₜ-cong e p X≈Y))

------------------------------------------------------------------------
-- F forms a dynamic asynchronous iteration

σₜ-isAsyncIterable : IsAsyncIterable _≈ₜ_ σₜ I
σₜ-isAsyncIterable = record
  { isDecEquivalenceᵢ = IndexedDecSetoid.isDecEquivalenceᵢ Decℝ𝕄ₛⁱ
  ; F-cong           = σₜ-cong
  }

δ∥ : AsyncIterable b ℓ n
δ∥ = record { isAsyncIterable = σₜ-isAsyncIterable }

------------------------------------------------------------------------
-- The asynchronous state function
--
-- Given a schedule "𝓢" and an initial state "X₀" then "δ 𝓢 X₀ t" is
-- the resulting state at time "t"

δ : Schedule n → RoutingMatrix → 𝕋 → RoutingMatrix
δ = asyncIter δ∥
