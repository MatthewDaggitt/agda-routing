open import Relation.Binary
import Relation.Binary.NonStrictToStrict as NSTS
open import Relation.Nullary using (¬_)


import RoutingLib.Relation.Binary.NonStrictToStrict.PartialOrder as PO
import RoutingLib.Relation.Binary.NonStrictToStrict as NSTS′

module RoutingLib.Relation.Binary.NonStrictToStrict.TotalOrder
  {a ℓ₁ ℓ₂} (totalOrder : TotalOrder a ℓ₁ ℓ₂) where

  open TotalOrder totalOrder

  ------------------------------------------------------------------------------
  -- Exports
  
  open PO (TotalOrder.poset totalOrder) public

  ≰⇒> : ∀ {x y} → ¬ (x ≤ y) → y < x
  ≰⇒> = NSTS′.≰⇒> _ _ Eq.sym reflexive total
