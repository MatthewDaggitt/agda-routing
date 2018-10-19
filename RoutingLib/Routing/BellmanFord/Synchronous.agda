open import Data.Nat using (ℕ)
open import Data.List using (foldr; tabulate)
open import Data.List.Relation.Pointwise using (tabulate⁺)

open import RoutingLib.Data.List.Relation.Pointwise using (foldr⁺)
open import RoutingLib.Iteration.Synchronous

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Model as Model using (AdjacencyMatrix)

module RoutingLib.Routing.BellmanFord.Synchronous
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n} (A : AdjacencyMatrix algebra n)
  where

open RawRoutingAlgebra algebra
open Model algebra n public

--------------------------------------------------------------------------------
-- Algorithm

-- Single iteration
σ : RoutingMatrix → RoutingMatrix
σ X i j = foldr _⊕_ (I i j) (tabulate (λ k → A i k ▷ X k j))

-- σ respects the underlying matrix equality
σ-cong : ∀ {X Y} → X ≈ₘ Y → σ X ≈ₘ σ Y
σ-cong X≈Y i j = foldr⁺
  _≈_ ⊕-cong ≈-refl (tabulate⁺ (λ k → ▷-cong (A i k) (X≈Y k j)))

-- Multiple iterations
σ^ : ℕ → RoutingMatrix → RoutingMatrix
σ^ = σ ^_
