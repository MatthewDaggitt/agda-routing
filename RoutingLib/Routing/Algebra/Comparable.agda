import Algebra.FunctionProperties as FunctionProperties
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Level using (_⊔_)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Algebra.FunctionProperties using (_Preservesᵇ_)
open import RoutingLib.Data.Matrix using (SquareMatrix)

open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.BellmanFord as BellmanFord

module RoutingLib.Routing.Algebra.Comparable
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) where

open RawRoutingAlgebra algebra
open FunctionProperties _≈_

-----------------------------------------------------------------------
-- Type

data Comparable : Rel Route (a ⊔ b) where
  00# : Comparable 0# 0#
  0∞  : Comparable 0# ∞
  ∞0  : Comparable ∞ 0#
  ∞∞  : Comparable ∞ ∞
  f0  : Comparable 0# {!!}
  0f  : Comparable 0# {!!}
  f∞  : Comparable {!!} ∞
  ∞f  : Comparable ∞ {!!}
  ff  : Comparable {!!} {!!}
{-
data WellFormed : Route → Set (a ⊔ b) where
  trivial : WellFormed 0#
  invalid : WellFormed ∞
  extend  : ∀ {n} {i j : Fin n} (f : Step i j) x → WellFormed (f ▷ x)
-}

-----------------------------------------------------------------------
-- Properties
{-
sel⇒WellFormed : Selective _⊕_ → _⊕_ Preservesᵇ WellFormed
sel⇒WellFormed = {!!}
-}
