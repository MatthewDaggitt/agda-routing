open import Data.Fin using (Fin)
open import Data.Product using (∃; _,_)
open import Function.Equality using (_⟨$⟩_)
open import Function.Injection using (_↣_; Injection)
open import Relation.Unary
open import Relation.Binary using (Setoid)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Function.Bijection using (_⤖_)

module RoutingLib.Relation.Unary where

_Preserves_ : ∀ {a p} {A : Set a} → (A → A) → Pred A p → Set _
f Preserves P = ∀ {a} → P a → P (f a)

_Forces_ : ∀ {a p} {A : Set a} → (A → A) → Pred A p → Set _
f Forces P = ∀ {a} → P (f a) → P a


Finite : ∀ {a p} {A : Set a} → Pred A p → Set _
Finite P = ∃ λ n → ∃ P ⤖ Fin n
