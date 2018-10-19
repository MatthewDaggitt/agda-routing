open import Relation.Binary
open import Data.Product using (proj₁)
import Relation.Binary.PreorderReasoning as PreR
import RoutingLib.Relation.Binary.NonStrictToStrict.PartialOrder as Strict
import RoutingLib.Relation.Binary.Reasoning.StrictCore as Core

module RoutingLib.Relation.Binary.Reasoning.PartialOrder
  {a ℓ₁ ℓ₂} (P : Poset a ℓ₁ ℓ₂) where

open Poset P
open Strict P

--------------------------------------------------------------------------------
-- Exports

open Core ≤-<-orderingPair public
