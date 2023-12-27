

module RoutingLib.Relation.Unary where

open import Data.Fin using (Fin)
open import Data.Product using (∃; _,_; _×_)
open import Function
open import Level using (Level)
open import Relation.Unary
open import Relation.Binary using (Setoid)
open import Relation.Nullary using (yes; no)

private
  variable
    a p q : Level
    A : Set a
    
_Preserves_ : (A → A) → Pred A p → Set _
f Preserves P = ∀ {a} → P a → P (f a)

_Forces_ : (A → A) → Pred A p → Set _
f Forces P = ∀ {a} → P (f a) → P a


Finite : Pred A p → Set _
Finite P = ∃ λ n → ∃ P ⤖ Fin n

_/_ : Pred A p → Pred A q → Pred A _
P / Q = λ x → x ∈ P × x ∉ Q
