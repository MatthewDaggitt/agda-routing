

open import Data.Nat using (zero; suc)
open import Data.Fin
open import Relation.Binary.PropositionalEquality using (cong; _≢_; refl)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_)

module RoutingLib.Data.Fin where

  ---------------------
  -- Added to stdlib --
  ---------------------
  
  -- The function f(i,j) = if j>i then j-1 else j
  punchdown : ∀ {m} {i j : Fin (suc m)} → i ≢ j → Fin m
  punchdown {_}     {zero}   {zero}  i≢j = contradiction refl i≢j
  punchdown {_}     {zero}   {suc j} _   = j
  punchdown {zero}  {suc ()}
  punchdown {suc m} {suc i}  {zero}  _   = zero
  punchdown {suc m} {suc i}  {suc j} i≢j = suc (punchdown (i≢j ∘ cong suc))

  -- The function f(i,j) = if j≥i then j+1 else j
  punchup : ∀ {m} → Fin (suc m) → Fin m → Fin (suc m)
  punchup zero    j       = suc j
  punchup (suc i) zero    = zero
  punchup (suc i) (suc j) = suc (punchup i j)
