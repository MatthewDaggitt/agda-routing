open import Data.Sum

module RoutingLib.Data.Sum where

  flip : ∀ {a b} {A : Set a} {B : Set b} → A ⊎ B → B ⊎ A
  flip (inj₁ x) = inj₂ x
  flip (inj₂ x) = inj₁ x
