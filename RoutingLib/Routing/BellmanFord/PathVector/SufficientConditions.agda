open import Level using (_⊔_) renaming (suc to lsuc)
open import Data.Product using (Σ; ∃; _×_; _,_)
open import Data.Sum using (_⊎_)
open import Relation.Binary using (_Preserves_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (Dec)
import Algebra.FunctionProperties as FunctionProperties

open import RoutingLib.Routing.Definitions
open import RoutingLib.Data.Graph.SimplePath2
  using (SimplePath; []; _∷ₐ_; valid; invalid)
  renaming (_≈_ to _≈ₚ_)

module RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions  where

  ----------------
  -- With paths --
  ----------------
  -- Sufficient conditions for the convergence of the synchronous
  -- Distributed Bellman Ford from any state when the algebra
  -- is lexed with paths

  record PathSufficientConditions
    {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
    {n} (𝓡𝓟 : RoutingProblem 𝓡𝓐 n) : Set (a ⊔ lsuc b ⊔ lsuc ℓ) where

    open RoutingProblem 𝓡𝓟
    open FunctionProperties _≈_
    
    field
      -- Operator properties
      ⊕-assoc     : Associative _⊕_
      ⊕-sel       : Selective   _⊕_
      ⊕-comm      : Commutative _⊕_
      ⊕-strictlyAbsorbs-▷ : ∀ s {r} → r ≉ 0# → ((s ▷ r) ⊕ r ≈ r) × (r ≉ s ▷ r)

      -- Element properties
      1#-anᵣ-⊕ : RightZero 1# _⊕_
      0#-an-▷  : ∀ f → f ▷ 0# ≈ 0#
      0#-idᵣ-⊕ : RightIdentity 0# _⊕_
      
      -- Path
      path           : ∀ r → SimplePath n
      path-cong      : path Preserves _≈_ ⟶ _≈ₚ_
      r≈1⇒path[r]≈[] : ∀ {r} → r ≈ 1# → path r ≈ₚ valid [] 
      r≈0⇒path[r]≈∅  : ∀ {r} → r ≈ 0# → path r ≈ₚ invalid
      path[r]≈∅⇒r≈0  : ∀ {r} → path r ≈ₚ invalid  → r ≈ 0#
      path-extension : ∀ i j r → path (A i j ▷ r) ≈ₚ ((i , j) ∷ₐ path r)
