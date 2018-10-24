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
open import RoutingLib.Iteration.Asynchronous.Dynamic
open import RoutingLib.Iteration.Asynchronous.Schedule using (Schedule; 𝕋; Epoch)
open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.Model as Model
import RoutingLib.Routing.BellmanFord.Synchronous as SynchronousBellmanFord

module RoutingLib.Routing.BellmanFord.Asynchronous
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n} (network : Epoch → Model.AdjacencyMatrix algebra n)
  where

open RawRoutingAlgebra algebra
open SynchronousBellmanFord algebra using (σ; σ-cong)

open Model algebra n public

------------------------------------------------------------------------
-- The adjacency matrix in each epoch, adjusted for participants

abstract

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

Fₜ : Epoch → Subset n → RoutingMatrix → RoutingMatrix
Fₜ e p X = σ (Aₜ e p) X

Fₜ-cong : ∀ e p {X Y} → X ≈ₘ[ p ] Y → Fₜ e p X ≈ₘ[ p ] Fₜ e p Y
Fₜ-cong e p X≈Y _ j = foldr⁺ _≈_ ⊕-cong ≈-refl (tabulate⁺ (Aₜ-cong e p X≈Y))

Fₜ-cong' : ∀ e p {X Y} → X ≈ₘ[ p ] Y → Fₜ e p X ≈ₘ Fₜ e p Y
Fₜ-cong' e p X≈Y _ j = foldr⁺ _≈_ ⊕-cong ≈-refl (tabulate⁺ (Aₜ-cong e p X≈Y))

Fₜ-cong-∉ : ∀ e p {X Y} {i} → i ∉ p → Fₜ e p X i ≈ₜ Fₜ e p Y i
Fₜ-cong-∉ e p {X} {Y} i∉p j = foldr⁺ _≈_ ⊕-cong ≈-refl (tabulate⁺ (λ k → Aₜ-reject-eq e _ k i∉p (X k j) (Y k j)))

postulate Fₜ-inactive : ∀ e {p} X → WellFormed p (Fₜ e p X)
-- Fₜ-inactive e {p} X {i} i∉p j = {!!}

------------------------------------------------------------------------
-- States in which the inactive nodes are actually inactive

X*-wf : ∀ e p {X*} → Fₜ e p X* ≈ₘ X* → WellFormed p X*
X*-wf e p {X*} FX*≈X* {i} i∉p = ≈ₜ-trans (≈ₘ-sym FX*≈X* i) (Fₜ-inactive e X* i∉p)

------------------------------------------------------------------------
-- F forms a dynamic asynchronous iteration

σ-isAsyncIterable : IsAsyncIterable _≈ₜ_ Fₜ I
σ-isAsyncIterable = record
  { isDecEquivalenceᵢ = IndexedDecSetoid.isDecEquivalenceᵢ Decℝ𝕄ₛⁱ
  ; F-cong           = Fₜ-cong
  ; F-inactive       = Fₜ-inactive
  }

δ∥ : AsyncIterable b ℓ n
δ∥ = record { isAsyncIterable = σ-isAsyncIterable }

------------------------------------------------------------------------
-- The asynchronous state function

δ : Schedule n → RoutingMatrix → 𝕋 → RoutingMatrix
δ = asyncIter δ∥
