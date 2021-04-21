open import RoutingLib.Routing.Prelude as RoutingPrelude using () renaming (AdjacencyMatrix to AdjacencyMatrix')
open import RoutingLib.Routing.Algebra

module RoutingLib.lmv34.Asynchronous.Omega_zero.Algebra
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n} (A : AdjacencyMatrix' algebra n)
  where

open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Relation.Nullary using (yes; no)

open import RoutingLib.lmv34.Synchronous.Gamma_zero.Algebra algebra n using (_⊕ₘ_; ⨁)
open RoutingPrelude algebra n
open RawRoutingAlgebra algebra

--------------------------------------------------------------------------------
-- Type definitions

-- Generalised Vector
Vectorᵢ : (Fin n → Set a) → Set a
Vectorᵢ Aᵢ = (i : Fin n) → Aᵢ i

--------------------------------------------------------------------------------
-- Operation definitions

-- Choice operator
infix 5 [_,_]_
[_,_]_ : ∀ {A : Fin n → Set a} → Vectorᵢ A → Vectorᵢ A → Subset n → Vectorᵢ A
([ X , Y ] S) i with (i ∈? S)
... | yes _ = X i
... | no  _ = Y i

-- Asynchronous (generalised) adjancency matrix application
_❪_❫ : AdjacencyMatrix → (Fin n → Fin n → Fin n → Route) → RoutingMatrix
(A ❪ f ❫) i j = ⨁ (λ k → (A i k) ▷ (f i k j))

-- Asynchronous (generalised) version of the Γ₀ operator
Γ₀' : (Fin n → RoutingMatrix) → RoutingMatrix
Γ₀' X = A ❪ X ❫ ⊕ₘ I
