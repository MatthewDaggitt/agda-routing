open import Data.Maybe
open import Data.Unit using (tt)
open import Relation.Nullary

module RoutingLib.Data.Maybe.Properties where

IsJust? : ∀ {a} {A : Set a} (x : Maybe A) → Dec (Is-just x)
IsJust? (just x) = yes (just tt)
IsJust? nothing  = no  (λ())
