open import Level using (_⊔_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec; []; _∷_; allFin; map; foldr)
open import Algebra.FunctionProperties using (Op₂)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (¬_)

open import RoutingLib.Routing.Definitions

module RoutingLib.Routing.Algorithms.DistributedBellmanFord 
  {a b ℓ n} (rp : RoutingProblem a b ℓ n) where

  open RoutingProblem rp

  -- A routing matrix --
  RMatrix : Set b
  RMatrix = Fin n → Fin n → Route

  -- Matrix addition
  _⊕ₘ_ : Op₂ RMatrix
  (A ⊕ₘ B) i j = A i j ⊕ B i j
  
  -- All the possible ways of forming paths from i to j
  -- by extending the paths held in the current RMatrix
  extensions : RMatrix → Fin n → Fin n → Vec Route n
  extensions X i j = map (λ k → A i k ▷ X k j) (allFin n)

  -- One update iteration
  σ : RMatrix → RMatrix
  σ X i j = foldr (λ _ → Route) _⊕_ (I i j) (extensions X i j)

  -- Multiple update iterations
  σ^ : ℕ → RMatrix → RMatrix
  σ^ zero    X = X
  σ^ (suc n) X = σ (σ^ n X)

  -- Equality between routing matrices
  _≈ₘ_ : Rel RMatrix ℓ
  A ≈ₘ B = ∀ i j → A i j ≈ B i j

  _≉ₘ_ : Rel RMatrix ℓ
  A ≉ₘ B = ¬ (A ≈ₘ B)

  
