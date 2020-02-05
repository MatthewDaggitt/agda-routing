
open import RoutingLib.Routing
open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.AdjacencyMatrix.Definitions
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n} (A : AdjacencyMatrix algebra n)
  where

open RawRoutingAlgebra algebra

open import Data.Product
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Binary.Construct.Closure.Transitive
  using () renaming (Plus′ to TransitiveClosure)
open import Relation.Nullary using (¬_)

open import RoutingLib.Data.Fin using (_+ₘ_; _-ₘ_)
open import RoutingLib.Data.FiniteSet using (⟦_∣_⟧) renaming (FiniteSet to FiniteSet⁺)

--------------------------------------------------------------------------------
-- Extends relation

-- x can be directly extended to form y
_↝_ : Route → Route → Set ℓ
x ↝ y = x ≉ ∞# × ∃₂ λ i j → A i j ▷ x ≈ y 

-- x can be strictly extended to form y
_↝ₛ_ : Route → Route → Set ℓ
x ↝ₛ y = x ↝ y × x ≉ y

-- x can be extended to form y
_↝*_ : Route → Route → Set _
_↝*_ = TransitiveClosure _↝_

--------------------------------------------------------------------------------
-- Threatens relation

infix 7 _◃_ _⊴_

-- In order to define a free network, we first define the threatens relation.
-- Route x threatens y if there exists some extension of x that is
-- preferred over y.
_⊴_ : Rel Route (a ⊔ ℓ)
x ⊴ y = ∃ λ z → x ↝ z × z ≤₊ y

_◃_ : Rel Route (a ⊔ ℓ)
x ◃ y = x ⊴ y × x ≉ y

--------------------------------------------------------------------------------
-- Types of adjacency matrices

-- A non-empty finite set of routes X is cyclic if every route
-- in the set can be extended and still be preferred to the previous route.
Cyclic : FiniteSet⁺ Route → Set _
Cyclic (⟦ _ ∣ X ⟧) = ∀ i → X (i -ₘ 1) ⊴ X i
  
-- A topology/adjacency matrix, is cycle free if there exists no cyclic set
-- of routes.
CycleFree : Set (a ⊔ ℓ)
CycleFree = ∀ X → ¬ Cyclic X
