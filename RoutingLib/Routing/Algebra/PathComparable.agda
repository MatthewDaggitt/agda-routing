import Algebra.FunctionProperties as FunctionProperties
open import Data.Nat using (ℕ) renaming (_≟_ to _≟ℕ_)
open import Data.Fin using (Fin)
open import Data.Maybe using (Maybe)
open import Level using (0ℓ; _⊔_)
open import Relation.Binary using (Rel; Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Algebra.FunctionProperties using (_Preservesᵇ_)
open import RoutingLib.Data.Maybe.Relation.Cross as Cross
open import RoutingLib.Data.Path.UncertifiedI

open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.Algebra.Comparable
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isPathAlgebra : IsPathAlgebra algebra)
  where

open RawRoutingAlgebra algebra
open IsPathAlgebra isPathAlgebra
open FunctionProperties _≈_

-----------------------------------------------------------------------
-- Type


{-
Comparable : Rel Route 0ℓ
Comparable x y = Cross _≡_ (source (path x)) (source (path y))

Comparable? : Decidable Comparable
Comparable? x y = Cross.dec _≟ℕ_ (source (path x)) (source (path y))

CompCommutative : Set (b ⊔ ℓ)
CompCommutative = ∀ {x y} → Comparable x y → x ⊕ y ≈ y ⊕ x

CompAssociative : Set (b ⊔ ℓ)
CompAssociative = {!∀ {x y} → Comparable x y → !}
-}
-----------------------------------------------------------------------
-- Properties

{-
sel⇒pres-comparable : Selective _⊕_ → _⊕_ Preservesᵇ WellFormed
sel⇒pres-comparable = {!!}
-}
