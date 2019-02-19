open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)

open import RoutingLib.Data.Matrix
open import RoutingLib.Data.Table using (Table)

module RoutingLib.db716.Data.Matrix where

  row : ∀ {a n} {A : Set a} → Fin n → SquareMatrix A n → Table A n 
  row i M = M i

  col : ∀ {a n} {A : Set a} → Fin n → SquareMatrix A n → Table A n
  col i M = λ j → M j i

  _ᵀ : ∀ {a n} {A : Set a} → SquareMatrix A n → SquareMatrix A n
  M ᵀ = λ i j → M j i
