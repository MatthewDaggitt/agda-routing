open import Relation.Binary using (Decidable; DecSetoid)
open import Relation.Binary.PropositionalEquality using (_≡_; decSetoid)

module RoutingLib.Data.List.Membership.DecPropositional
  {a} {A : Set a} (_≟_ : Decidable {A = A} _≡_) where

  DS : DecSetoid a _
  DS = decSetoid _≟_

  open import RoutingLib.Data.List.Membership.DecSetoid DS public
