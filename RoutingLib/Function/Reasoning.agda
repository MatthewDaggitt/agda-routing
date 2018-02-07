
module RoutingLib.Function.Reasoning where

  open import Function using (_∋_)
  open import RoutingLib.Function using (_∣>_; _∣>′_) public 

  infixl 0 ∋-syntax
  ∋-syntax = _∋_
  syntax ∋-syntax A a = a ∶ A
