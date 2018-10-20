open import Data.Fin using (Fin)
open import Data.Product using (∃; _,_)
open import Function.Bijection using (_⤖_)

module RoutingLib.Relation.Nullary where

Finite : ∀ {a} (A : Set a) → Set _
Finite P = ∃ λ n → P ⤖ Fin n

