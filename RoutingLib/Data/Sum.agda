open import Data.Sum

module RoutingLib.Data.Sum where

  -- stdlib
  swap : ∀ {a b} {A : Set a} {B : Set b} → A ⊎ B → B ⊎ A
  swap (inj₁ x) = inj₂ x
  swap (inj₂ x) = inj₁ x
