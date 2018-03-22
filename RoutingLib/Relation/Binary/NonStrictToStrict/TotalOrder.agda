open import Relation.Binary
import RoutingLib.Relation.Binary.NonStrictToStrict.PartialOrder as PO

module RoutingLib.Relation.Binary.NonStrictToStrict.TotalOrder
  {a ℓ₁ ℓ₂} (totalOrder : TotalOrder a ℓ₁ ℓ₂) where

  open PO (TotalOrder.poset totalOrder) public
  
