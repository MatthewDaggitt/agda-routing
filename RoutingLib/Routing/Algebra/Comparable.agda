import Algebra.FunctionProperties as FunctionProperties
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Level using (_⊔_)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Algebra.FunctionProperties using (_Preservesᵇ_)
open import RoutingLib.Data.Matrix using (SquareMatrix)

open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.Algebra.Comparable
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) where

open RawRoutingAlgebra algebra
open FunctionProperties _≈_

-----------------------------------------------------------------------
-- Type

data Comparable : Rel Route (a ⊔ b) where
  00# : Comparable 0# 0#
  0∞# : Comparable 0# ∞
  ∞0# : Comparable ∞ 0#
  ∞∞# : Comparable ∞ ∞
  e0# : ∀ {n} {i j : Fin n} (f : Step i j) (x : Route) → Comparable 0# (f ▷ x)
  0e# : ∀ {n} {i j : Fin n} (f : Step i j) (x : Route) → Comparable (f ▷ x) 0#
  ∞e# : ∀ {n} {i j : Fin n} (f : Step i j) (x : Route) → Comparable ∞ (f ▷ x)
  e∞# : ∀ {n} {i j : Fin n} (f : Step i j) (x : Route) → Comparable (f ▷ x) ∞
  ee# : ∀ {n} {i j k : Fin n} (f : Step i j) (g : Step i k) (x y : Route) → j ≢ k → Comparable (f ▷ x) (g ▷ y)

-----------------------------------------------------------------------
-- Properties

{-
sel⇒pres-comparable : Selective _⊕_ → _⊕_ Preservesᵇ WellFormed
sel⇒pres-comparable = {!!}
-}
