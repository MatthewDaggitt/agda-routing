
module RoutingLib.Data.Fin where

open import Data.Fin hiding (_+_)
open import Data.Nat.Base
open import Data.Nat.DivMod

private
  variable
    n : ℕ

_+ₘ_ : Fin n → ℕ → Fin n
_+ₘ_ {n@(suc _)} i m = (toℕ i + m) mod n

_-ₘ_ : Fin n → ℕ → Fin n
i     -ₘ zero  = i
zero  -ₘ suc m = fromℕ _ -ₘ m
suc i -ₘ suc m = inject₁ i -ₘ m
