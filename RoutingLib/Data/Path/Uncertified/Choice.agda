

module RoutingLib.Data.Path.Uncertified.Choice where

open import Algebra.FunctionProperties
open import Relation.Binary.PropositionalEquality

open import RoutingLib.Data.Path.Uncertified
open import RoutingLib.Data.Path.Uncertified.Properties
open import RoutingLib.Algebra.Construct.NaturalChoice.Min.TotalOrder as Min

abstract

  open module Minₗₑₓ = Min ≤ₗₑₓ-totalOrder public
    renaming
    ( _⊓_     to _⊓ₗₑₓ_
    ; ⊓-sel   to ⊓ₗₑₓ-sel
    ; ⊓-comm  to ⊓ₗₑₓ-comm
    ; ⊓-assoc to ⊓ₗₑₓ-assoc
    )

  ⊓ₗₑₓ-zeroʳ : RightZero _≡_ [] _⊓ₗₑₓ_
  ⊓ₗₑₓ-zeroʳ = Minₗₑₓ.⊓-zeroʳ ≤ₗₑₓ-minimum
