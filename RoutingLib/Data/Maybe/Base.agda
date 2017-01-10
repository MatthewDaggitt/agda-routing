open import Data.Bool using (Bool; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)

module RoutingLib.Data.Maybe.Base where

  predBoolToMaybe : ∀ {a} {A : Set a} → (A → Bool) → A → Maybe A
  predBoolToMaybe P x = if P x then just x else nothing
