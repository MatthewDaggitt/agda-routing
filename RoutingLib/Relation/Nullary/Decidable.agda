open import Relation.Nullary
open import Data.Sum

module RoutingLib.Relation.Nullary.Decidable where

  toSum : ∀ {p} {P : Set p} → Dec P → P ⊎ ¬ P
  toSum (yes p) = inj₁ p
  toSum (no ¬p) = inj₂ ¬p
