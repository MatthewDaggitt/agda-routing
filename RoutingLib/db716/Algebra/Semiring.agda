open import Algebra using (Semiring)

module RoutingLib.db716.Algebra.Semiring {c ℓ} (S : Semiring c ℓ) where
open import Data.Nat using (ℕ; suc)

open Semiring S

pow : Carrier → ℕ → Carrier
pow x 0 = 1#
pow x 1 = x
pow x (suc (suc k)) = x * pow x (suc k)

powSum : Carrier → ℕ → Carrier
powSum x 0 = 1#
powSum x (suc n) = powSum x n + pow x (suc n)


