open import Relation.Nullary
open import Data.Sum hiding ([_,_])

module RoutingLib.Relation.Nullary.Decidable where

  toSum : ∀ {p} {P : Set p} → Dec P → P ⊎ ¬ P
  toSum (yes p) = inj₁ p
  toSum (no ¬p) = inj₂ ¬p

  [_,_] : ∀ {a b} {A : Set a} {B : Set b} →
        (A → B) → (¬ A → B) →
        (Dec A → B)
  [ f , g ] (yes A) = f A
  [ f , g ] (no ¬A) = g ¬A
