

module RoutingLib.Data.Sum where

open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Level using (Level)
open import Relation.Nullary using (yes; no)
open import Relation.Unary using (Decidable)

private
  variable
    a : Level
    A B : Set a

IsInj₁ : A ⊎ B → Set
IsInj₁ (inj₁ x) = ⊤
IsInj₁ (inj₂ y) = ⊥

IsInj₂ : A ⊎ B → Set
IsInj₂ (inj₁ x) = ⊥
IsInj₂ (inj₂ y) = ⊤

isInj₁? : Decidable (IsInj₁ {A = A} {B = B})
isInj₁? (inj₁ x) = yes _
isInj₁? (inj₂ y) = no λ()

isInj₂? : Decidable (IsInj₂ {A = A} {B = B})
isInj₂? (inj₁ x) = no λ()
isInj₂? (inj₂ y) = yes _
