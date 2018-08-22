import Algebra.FunctionProperties as FunctionProperties
open import Data.Nat using (ℕ)
import Data.Fin as Fin
open import Level using (_⊔_)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Algebra.FunctionProperties using (_Preservesᵇ_)
open import RoutingLib.Data.Matrix using (SquareMatrix)

open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.BellmanFord as BellmanFord

module RoutingLib.Routing.Algebra.WellFormed
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) where
  -- (A : SquareMatrix (RawRoutingAlgebra.Step algebra) n) where

open RawRoutingAlgebra algebra
-- open BellmanFord algebra A
open FunctionProperties _≈_

-----------------------------------------------------------------------
-- Type

data WellFormed : Route → Set (a ⊔ b) where
  trivial : WellFormed 0#
  invalid : WellFormed ∞
  extend  : ∀ f x → WellFormed (f ▷ x)

-----------------------------------------------------------------------
-- Properties
{-
sel⇒WellFormed : Selective _⊕_ → _⊕_ Preservesᵇ WellFormed
sel⇒WellFormed = {!!}
-}
