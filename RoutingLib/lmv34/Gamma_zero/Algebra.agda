open import Algebra.FunctionProperties.Core using (Op₂)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin)
open import Data.List using (foldr; tabulate)

open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra)
import RoutingLib.Routing as Routing

module RoutingLib.lmv34.Gamma_zero.Algebra
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) (n : ℕ)
  where

open Routing algebra n
open RawRoutingAlgebra algebra

------------------------------------
-- Operation definitions

-- Matrix addition
infixl 10 _⊕ₘ_
_⊕ₘ_ : Op₂ RoutingMatrix
(A ⊕ₘ B) i j = (A i j) ⊕ (B i j)

-- Big choice operator
infix 5 ⨁
⨁ : ∀ {k} → (Fin k → Route) → Route
⨁ iter = foldr _⊕_ ∞# (tabulate iter)

--------------------------------------
-- Asynchronous

open import Data.Fin.Subset using (Subset)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Vec.Functional using (Vector)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Iteration.Asynchronous.Static using (AsyncIterable; asyncIter)
open import RoutingLib.Iteration.Asynchronous.Static.Schedule using (Schedule; 𝕋)

[_,_]_ : ∀ {a} {A : Set a} {n} → Vector A n → Vector A n → Subset n → Vector A n
([ X , Y ] S) i with (i ∈? S)
... | yes _ = X i
... | no _  = Y i

-- Generalised adjancency matrix application
_❪_❫ : AdjacencyMatrix → (Fin n → Fin n → Fin n → Route) → RoutingMatrix
(A ❪ f ❫) i j = ⨁ (λ k → (A i k) ▷ (f i k j))

-- Matrix application
infix 11 _〔_〕
_〔_〕 : AdjacencyMatrix → RoutingMatrix → RoutingMatrix
A 〔 X 〕 = A ❪ (λ i k j → X k j) ❫
