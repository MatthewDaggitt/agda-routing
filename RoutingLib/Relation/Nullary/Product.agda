module RoutingLib.Relation.Nullary.Product where

open import Data.Product
open import Relation.Nullary
open import Function using (_∘_)


~-dec : ∀ {p q} {P : Set p} {Q : Set q} → Dec (P × Q) → Dec (Q × P)
~-dec (yes p) = yes (swap p)
~-dec (no ¬p) = no (¬p ∘ swap)
