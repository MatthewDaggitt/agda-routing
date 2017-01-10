
open import Algebra.FunctionProperties using (Op₂)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; suc)
open import Level using (_⊔_) renaming (suc to lsuc)
open import Relation.Nullary using (¬_)
open import Relation.Binary using (Rel; IsDecEquivalence; Setoid)

open import RoutingLib.Algebra.FunctionProperties using (_Preserves_; _Preservesₗ_)

module RoutingLib.Routing.Definitions where
  
  ---------------------
  -- Routing algebra --
  ---------------------
  -- A routing algebra represents the underlying algebra for a set of routing problems.

  record RoutingAlgebra a b ℓ : Set (lsuc (a ⊔ b ⊔ ℓ)) where
  
    infix 7 _⊕_
    infix 6 _▷_
    infix 4 _≈_ _≉_

    field
      Step  : Set a
      Route : Set b
      _⊕_ : Op₂ Route
      _▷_ : Step → Route → Route
      
      _≈_ : Rel Route ℓ
      ≈-isDecEquivalence : IsDecEquivalence _≈_
      ⊕-pres-≈ : _⊕_ Preserves _≈_
      ▷-pres-≈ : _▷_ Preservesₗ _≈_

    -- A few useful consequences of equality to export
    _≉_ : Rel Route ℓ
    x ≉ y = ¬ (x ≈ y) 

    open IsDecEquivalence ≈-isDecEquivalence public
  
    S : Setoid b ℓ
    S = record {
        _≈_ = _≈_; 
        isEquivalence = isEquivalence
      }



  ---------------------
  -- Routing problem --
  ---------------------
  -- An instantiation of a specific routing problem for a routing algebra
  -- In particular we need an adjacency matrix (representing the topology)
  -- and an identity matrix

  record RoutingProblem a b ℓ (n : ℕ) : Set (lsuc (a ⊔ b ⊔ ℓ)) where

    field
      ra : RoutingAlgebra a b ℓ
      A : Fin n → Fin n → RoutingAlgebra.Step ra
      I : Fin n → Fin n → RoutingAlgebra.Route ra

    open RoutingAlgebra ra public
