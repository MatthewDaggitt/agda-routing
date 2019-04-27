

module RoutingLib.Relation.Nullary.Negation where

open import Data.Sum
open import Relation.Nullary
open import Relation.Nullary.Negation

contradiction₂ : ∀ {p q w} {P : Set p} {Q : Set q} {Whatever : Set w} →
                P ⊎ Q → ¬ P → ¬ Q → Whatever
contradiction₂ (inj₁ p) ¬p ¬q = contradiction p ¬p
contradiction₂ (inj₂ q) ¬p ¬q = contradiction q ¬q
