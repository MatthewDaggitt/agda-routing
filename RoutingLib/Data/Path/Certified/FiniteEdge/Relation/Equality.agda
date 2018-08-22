open import Data.Nat using (ℕ)
open import Level using () renaming (zero to ℓ₀)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_; yes; no)

open import RoutingLib.Data.SimplePath
open import RoutingLib.Data.SimplePath.NonEmpty using (SimplePathⁿᵗ)
import RoutingLib.Data.SimplePath.NonEmpty.Relation.Equality as NE

module RoutingLib.Data.SimplePath.Relation.Equality where

  module _ {n : ℕ} where

    ----------------------------------------------------------------------------
    -- Relations


    ----------------------------------------------------------------------------
    -- Properties
