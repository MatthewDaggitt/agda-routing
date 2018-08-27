open import Algebra.FunctionProperties
open import Data.Fin using (Fin)
open import Level using (_⊔_)

open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.Algebra.RoutingAlgebra
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  where

open RawRoutingAlgebra algebra

--------------------------------------------------------------------------------
-- Algebras that represent distance-vector protocols

record IsRoutingAlgebra : Set (a ⊔ b ⊔ ℓ) where
  no-eta-equality -- Needed due to bug #2732 in Agda

  field
    ⊕-sel        : Selective _≈_ _⊕_
    ⊕-comm       : Commutative _≈_ _⊕_
    ⊕-assoc      : Associative _≈_ _⊕_
    ⊕-zeroʳ      : RightZero _≈_ 0# _⊕_
    ⊕-identityʳ  : RightIdentity _≈_ ∞ _⊕_
    ▷-fixedPoint : ∀ {n} {i j : Fin n} (f : Step i j) → f ▷ ∞ ≈ ∞
