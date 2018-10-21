open import Relation.Binary
import Relation.Binary.Construct.NonStrictToStrict as NSTS

import RoutingLib.Relation.Binary.Construct.NonStrictToStrict.TotalOrder as TO

module RoutingLib.Relation.Binary.Construct.NonStrictToStrict.DecTotalOrder
  {a ℓ₁ ℓ₂} (decTotalOrder : DecTotalOrder a ℓ₁ ℓ₂) where

  open DecTotalOrder decTotalOrder

  ------------------------------------------------------------------------------
  -- Exports

  open TO (DecTotalOrder.totalOrder decTotalOrder) public

  <-strictTotalOrder : StrictTotalOrder a ℓ₁ _
  <-strictTotalOrder = record
    { isStrictTotalOrder = NSTS.<-isStrictTotalOrder₂ _ _ isDecTotalOrder
    }


  <-cmp : Trichotomous _≈_ _<_
  <-cmp = NSTS.<-trichotomous _ _ Eq.sym _≟_ antisym total

  open StrictTotalOrder <-strictTotalOrder public
    using (_<?_)
    renaming
    ( isStrictTotalOrder to <-isStrictTotalOrder
    )
