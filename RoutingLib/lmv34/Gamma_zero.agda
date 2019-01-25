open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Level renaming (suc to lsuc)

module RoutingLib.lmv34.Gamma_zero {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) (n : ℕ)  where

open RawRoutingAlgebra algebra

RoutingMatrix : Set b
RoutingMatrix = Fin n → Fin n → Route

record Γ₀-State : Set (lsuc b) where
  field
    X : RoutingMatrix

