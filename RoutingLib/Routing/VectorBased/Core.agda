open import Data.Nat using (ℕ)
open import Data.List using (foldr; tabulate)
open import Data.List.Relation.Pointwise using (tabulate⁺)

open import RoutingLib.Data.List.Relation.Binary.Pointwise using (foldr⁺)
open import RoutingLib.Iteration.Synchronous

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing as Routing using (AdjacencyMatrix)

module RoutingLib.Routing.VectorBased.Core
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n} (A : AdjacencyMatrix algebra n)
  where

open RawRoutingAlgebra algebra
open Routing algebra n

--------------------------------------------------------------------------------
-- Algorithm

-- Single iteration
F : RoutingMatrix → RoutingMatrix
F X i j = foldr _⊕_ (I i j) (tabulate (λ k → A i k ▷ X k j))

-- F respects the underlying matrix equality
F-cong : ∀ {X Y} → X ≈ₘ Y → F X ≈ₘ F Y
F-cong X≈Y i j = foldr⁺ _≈_ ⊕-cong ≈-refl (tabulate⁺ (λ k → ▷-cong _ (X≈Y k j)))
