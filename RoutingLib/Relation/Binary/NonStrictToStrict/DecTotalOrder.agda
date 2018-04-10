open import Relation.Binary
import Relation.Binary.NonStrictToStrict as NSTS

import RoutingLib.Relation.Binary.NonStrictToStrict.TotalOrder as TO

module RoutingLib.Relation.Binary.NonStrictToStrict.DecTotalOrder
  {a ℓ₁ ℓ₂} (decTotalOrder : DecTotalOrder a ℓ₁ ℓ₂) where
  
  open DecTotalOrder decTotalOrder

  ------------------------------------------------------------------------------
  -- Exports

  open TO (DecTotalOrder.totalOrder decTotalOrder) public
  
  <-strictTotalOrder : StrictTotalOrder a ℓ₁ _
  <-strictTotalOrder = record
    { isStrictTotalOrder = NSTS.isDecTotalOrder⟶isStrictTotalOrder _ _ isDecTotalOrder
    }
  
  open StrictTotalOrder <-strictTotalOrder public
    using (_<?_)
    renaming
    ( isStrictTotalOrder to <-isStrictTotalOrder
    )
