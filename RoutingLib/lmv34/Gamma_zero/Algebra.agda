open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Algebra.FunctionProperties.Core
open import Data.List using (foldr; tabulate)

open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra)
import RoutingLib.Routing as Routing

module RoutingLib.lmv34.Gamma_zero.Algebra {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) (n : ℕ) where

open Routing algebra n
open RawRoutingAlgebra algebra

-- Matrix addition
infixl 9 _M⊕_
_M⊕_ : Op₂ RoutingMatrix
A M⊕ B  = λ i j → (A i j) ⊕ (B i j)

-- Big choice operator
infix 5 Σ⊕
Σ⊕ : ∀ {n} (f : Fin n → Route) → Route
Σ⊕ f = foldr _⊕_ ∞ (tabulate f)

-- Matrix application
infix 10 _〚_〛
_〚_〛 : AdjacencyMatrix → RoutingMatrix → RoutingMatrix
(A 〚 X 〛) i j = Σ⊕ (λ k → (A i k) ▷ (X k j))
