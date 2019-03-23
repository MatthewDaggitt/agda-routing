open import Relation.Binary.PropositionalEquality using (setoid)

open import RoutingLib.Data.List.Relation.Unary.Uniqueness.Setoid as SetoidUniqueness

module RoutingLib.Data.List.Relation.Unary.Uniqueness.Propositional {a} {A : Set a} where

  open SetoidUniqueness (setoid A) public
