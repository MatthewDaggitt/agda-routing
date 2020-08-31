
module RoutingLib.Data.List.Relation.Unary.Unique.Propositional.Properties where

open import Data.List
open import Data.List.Relation.Unary.Unique.Propositional
open import Level
open import Relation.Binary.PropositionalEquality using (decSetoid)

open import RoutingLib.Data.List
import RoutingLib.Data.List.Relation.Unary.Unique.Setoid.Properties as SP

private
  variable
    a : Level
    A : Set a

deduplicate⁺ : ∀ _≟_ (xs : List A) → Unique (deduplicate _≟_ xs)
deduplicate⁺ _≟_ = SP.deduplicate⁺ (decSetoid _≟_)
