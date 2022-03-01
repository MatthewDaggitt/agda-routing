


module RoutingLib.Data.Nat.Divisibility where

open import Data.Nat
open import Data.Nat.Divisibility
open import Data.Nat.DivMod

open import RoutingLib.Data.Nat.DivMod

-- stdlib v2.0
m∸m%n∣n : ∀ m n {n≢0} → n ∣ m ∸ ((m % n) {n≢0})
m∸m%n∣n m n@(suc n-1) = m%n≡0⇒n∣m (m ∸ m % n) n-1 ([m∸m%n]%n≡0 m n-1)
