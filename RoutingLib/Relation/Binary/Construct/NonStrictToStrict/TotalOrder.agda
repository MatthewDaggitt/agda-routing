open import Relation.Binary
import Relation.Binary.Construct.NonStrictToStrict as NSTS
open import Relation.Nullary using (¬_)
open import Data.Sum using (inj₁; inj₂)


import RoutingLib.Relation.Binary.Construct.NonStrictToStrict.PartialOrder as PO
import RoutingLib.Relation.Binary.Construct.NonStrictToStrict as NSTS′

module RoutingLib.Relation.Binary.Construct.NonStrictToStrict.TotalOrder
  {a ℓ₁ ℓ₂} (totalOrder : TotalOrder a ℓ₁ ℓ₂) where

  open TotalOrder totalOrder

  ------------------------------------------------------------------------------
  -- Exports

  open PO (TotalOrder.poset totalOrder) public

  ≰⇒> : ∀ {x y} → ¬ (x ≤ y) → y < x
  ≰⇒> = NSTS.≰⇒> _ _ Eq.sym reflexive total

