
open import Data.Product
open import Data.Fin using (Fin)
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Binary.Construct.Closure.Transitive
open import Relation.Nullary using (¬_)

open import RoutingLib.Routing
open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.AdjacencyMatrix.Relations
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n} (A : AdjacencyMatrix algebra n)
  where

open RawRoutingAlgebra algebra

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
_↝*_ = TransClosure _↝_

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
