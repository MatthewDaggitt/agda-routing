open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Level renaming (suc to lsuc)

module RoutingLib.lmv34.Gamma_zero {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) (n : ℕ)  where

open RawRoutingAlgebra algebra

RoutingMatrix : (B : Set b) → ℕ → ℕ → Set b
RoutingMatrix B x y = (i : Fin x) → (j : Fin y) → B

record Γ₀-State : Set (lsuc b) where
  field
    X : {B : Set b} → RoutingMatrix B n n
