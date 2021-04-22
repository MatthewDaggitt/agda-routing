open import Algebra.Core using (Op₂)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin)
open import Data.List using (foldr; tabulate)

open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra)
import RoutingLib.Routing.Prelude as RoutingPrelude

module RoutingLib.lmv34.Synchronous.Gamma_zero.Algebra
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) (n : ℕ)
  where

open RoutingPrelude algebra n
open RawRoutingAlgebra algebra

------------------------------------
-- Operation definitions

-- Matrix addition
infixl 10 _⊕ₘ_
_⊕ₘ_ : Op₂ RoutingMatrix
(A ⊕ₘ B) i j = (A i j) ⊕ (B i j)

-- Big choice operator
infix 5 ⨁
⨁ : ∀ {k} → (Fin k → PathWeight) → PathWeight
⨁ iter = foldr _⊕_ ∞# (tabulate iter)

-- Matrix application
infix 11 _〔_〕
_〔_〕 : AdjacencyMatrix → RoutingMatrix → RoutingMatrix
(A 〔 X 〕) i j = ⨁ (λ k → (A i k) ▷ (X k j))
