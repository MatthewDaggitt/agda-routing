open import Level using (_⊔_)
open import Algebra.FunctionProperties using (Associative; Commutative; RightZero; Selective)

open import RoutingLib.Routing.Definitions

module RoutingLib.Routing.BellmanFord.PathsConvergence.SufficientConditions  where

  ----------------
  -- With paths --
  ----------------
  -- Sufficient conditions for the convergence of the synchronous
  -- Distributed Bellman Ford from any state when the algebra
  -- is lexed with paths

  record SufficientConditions {a b ℓ} (ra : RoutingAlgebra a b ℓ) : Set (a ⊔ b ⊔ ℓ) where

    open RoutingAlgebra ra

    field
      -- Operator properties
      ⊕-assoc     : Associative _≈_ _⊕_
      ⊕-sel       : Selective   _≈_ _⊕_
      ⊕-comm      : Commutative _≈_ _⊕_
      ⊕-absorbs-▷ : ∀ s r → (s ▷ r) ⊕ r ≈ r

      -- Element properties
      1#-anᵣ-⊕ : RightZero _≈_ 1# _⊕_
