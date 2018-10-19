open import Data.Fin using (Fin)
open import Data.Product using (∃; _,_)
open import Function.Equality using (_⟨$⟩_)
open import Function.Injection using (_↣_; Injection)
open import Relation.Unary
open import Relation.Binary using (Setoid)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Function.Bijection using (_⤖_)

module RoutingLib.Relation.Nullary where

Finite : ∀ {a} (A : Set a) → Set _
Finite P = ∃ λ n → P ⤖ Fin n

