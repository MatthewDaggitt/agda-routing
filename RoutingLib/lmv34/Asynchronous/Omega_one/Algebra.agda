open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
open import RoutingLib.Routing as Routing using () renaming (AdjacencyMatrix to AdjacencyMatrix')

module RoutingLib.lmv34.Asynchronous.Omega_one.Algebra
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  {n} (A : AdjacencyMatrix' algebra n)
  where

open import Data.Fin using (Fin)

open import RoutingLib.lmv34.Synchronous.Gamma_one.Algebra isRoutingAlgebra n

open RawRoutingAlgebra algebra using (_▷_)
open Routing algebra n using (AdjacencyMatrix; RoutingMatrix; I)

--------------------------------------------------------------------------------
-- Operation definitions

-- Generalised (asynchronous) matrix multiplication
_⟦_⟧' : AdjacencyMatrix → (Fin n → Fin n → RoutingSet) → RoutingVector
(A ⟦ f ⟧') i = ⨁ₛ (λ q → (A i q ▷_) [ f i q ])

-- Generalised (asynchronous) operator
Γ₁' : (Fin n → Fin n → RoutingSet) → RoutingVector
Γ₁' f = A ⟦ f ⟧' ⊕ᵥ ~ I

─' : (Fin n → RoutingVector) → (Fin n → RoutingMatrix)
─' V i = (─ V i)

~' : (Fin n → RoutingMatrix) → (Fin n → RoutingVector)
~' X i = (~ X i)
