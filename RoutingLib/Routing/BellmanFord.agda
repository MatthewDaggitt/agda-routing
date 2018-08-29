open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List using (foldr; tabulate)
open import Data.List.Relation.Pointwise using (tabulate⁺)
open import Data.Product using (_×_)
open import Relation.Binary using (Setoid; DecSetoid)
open import Relation.Nullary using (yes; no)


open import RoutingLib.Asynchronous using (Parallelisation)
open import RoutingLib.Data.Table using (Table)
open import RoutingLib.Data.List.Relation.Pointwise
  using (foldr⁺)
open import RoutingLib.Function.Iteration
import RoutingLib.Data.Table.Relation.DecidableEquality as TableDecEquality
open import RoutingLib.Data.Matrix
import RoutingLib.Data.Matrix.Relation.DecidableEquality as MatrixDecEquality
open import RoutingLib.Relation.Binary.Indexed.Homogeneous as I using (triviallyIndexSetoid)

open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.BellmanFord
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n} (A : AdjacencyMatrix algebra n)
  where

open RawRoutingAlgebra algebra

--------------------------------------------------------------------------------
-- Definitions

RTable : Set b
RTable = Table Route n

RMatrix : Set b
RMatrix = SquareMatrix Route n

--------------------------------------------------------------------------------
-- Equality

open MatrixDecEquality DS public
open TableDecEquality DS using (𝕋ₛ;_≟ₜ_) public

ℝ𝕋ₛ : Setoid b ℓ
ℝ𝕋ₛ = 𝕋ₛ n

ℝ𝕋ₛⁱ : I.Setoid (Fin n) _ _
ℝ𝕋ₛⁱ = triviallyIndexSetoid (Fin n) S

ℝ𝕄ₛ : Setoid b ℓ
ℝ𝕄ₛ = 𝕄ₛ n n

ℝ𝕄ₛⁱ : I.Setoid (Fin n) _ _
ℝ𝕄ₛⁱ = triviallyIndexSetoid (Fin n) ℝ𝕋ₛ

Decℝ𝕄ₛ : DecSetoid b ℓ
Decℝ𝕄ₛ = Dec𝕄ₛ n n

--------------------------------------------------------------------------------
-- Algorithm

-- Identity matrix
I : RMatrix
I i j with j ≟ᶠ i
... | yes _ = 0#
... | no  _ = ∞

-- Single iteration
σ : RMatrix → RMatrix
σ X i j = foldr _⊕_ (I i j) (tabulate (λ k → A i k ▷ X k j))

-- σ respects the underlying matrix equality
σ-cong : ∀ {X Y} → X ≈ₘ Y → σ X ≈ₘ σ Y
σ-cong X≈Y i j = foldr⁺
  _≈_ ⊕-cong ≈-refl (tabulate⁺ (λ k → ▷-cong (A i k) (X≈Y k j)))

-- Multiple iterations
σ^ : ℕ → RMatrix → RMatrix
σ^ = σ ^ˡ_

-- Parallelisation of algorithm
σ∥ : Parallelisation ℝ𝕄ₛⁱ
σ∥ = record { F = σ }

open Parallelisation σ∥ using () renaming (asyncIter to δ) public
