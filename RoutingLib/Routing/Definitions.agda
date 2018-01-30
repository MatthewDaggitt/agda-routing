open import Algebra.FunctionProperties using (Op₂; Congruent₂)
open import Data.Fin using (Fin)
open import Data.List using (List)
import Data.List.Any.Membership as Membership
open import Data.Nat using (ℕ)
open import Data.Product using (∃; _,_; _×_; Σ)
open import Data.Maybe
open import Function.Equality using (_⟶_; Π)
open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary using (Rel; IsDecEquivalence; Setoid; DecSetoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import RoutingLib.Algebra.FunctionProperties using (_Preservesₗ_)
open import RoutingLib.Data.List.Membership.Propositional.Properties using (∈-concat⁺; ∈-tabulate⁺)
open import RoutingLib.Data.List.Uniqueness.Setoid using (Unique)
open import RoutingLib.Data.Matrix using (SquareMatrix; Matrix)
open import RoutingLib.Data.Table using (Table)
open import RoutingLib.Data.Graph.SimplePath2 using (SimplePath; valid; invalid; []; _∷_; _∷_∣_∣_) renaming (_≈_ to _≈ₚ_)
open import RoutingLib.Data.Graph.SimplePath.Properties using (p≈q⇒p₀≡q₀)
import RoutingLib.Algebra.Selectivity.RightNaturalOrder as RightNaturalOrder

module RoutingLib.Routing.Definitions where

  ---------------------
  -- Routing algebra --
  ---------------------
  -- A routing algebra represents the underlying algebra for a set of routing problems.

  record RoutingAlgebra a b ℓ : Set (lsuc (a ⊔ b ⊔ ℓ)) where
    no-eta-equality -- Needed due to bug #2732 in Agda
    
    infix 7 _⊕_
    infix 6 _▷_
    infix 4 _≈_ _≉_

    field
      Step  : Set a
      Route : Set b
      _⊕_   : Op₂ Route
      _▷_   : Step → Route → Route
      0#    : Route
      1#    : Route

      _≈_                : Rel Route ℓ
      ≈-isDecEquivalence : IsDecEquivalence _≈_
      ⊕-cong             : Congruent₂ _≈_ _⊕_
      ▷-cong             : _▷_ Preservesₗ _≈_
      1≉0                : ¬ (1# ≈ 0#)
      
    -- A few useful consequences of equality to export
    _≉_ : Rel Route ℓ
    x ≉ y = ¬ (x ≈ y)

    open IsDecEquivalence ≈-isDecEquivalence renaming
      ( refl          to ≈-refl
      ; reflexive     to ≈-reflexive
      ; sym           to ≈-sym
      ; trans         to ≈-trans
      ; isEquivalence to ≈-isEquivalence
      ) public

    S : Setoid b ℓ
    S = record 
      { _≈_           = _≈_
      ; isEquivalence = ≈-isEquivalence
      }

    DS : DecSetoid b ℓ
    DS = record 
      { Carrier = Route 
      ; _≈_ = _≈_ 
      ; isDecEquivalence = ≈-isDecEquivalence 
      }    
    
    open RightNaturalOrder _≈_ _⊕_ using () renaming
      ( _≤_ to _≤₊_
      ; _≰_ to _≰₊_
      ; _<_ to _<₊_
      )
      public
    
  
  ---------------------
  -- Routing problem --
  ---------------------
  -- An instantiation of a specific routing problem for a routing algebra
  -- In particular we need an adjacency matrix (representing the topology)

  record RoutingProblem
    {a b ℓ} (𝓡𝓐 : RoutingAlgebra a b ℓ) (n : ℕ)
    : Set (lsuc (a ⊔ b ⊔ ℓ)) where
    no-eta-equality -- Needed due to bug #2732 in Agda
    
    field
      A  : SquareMatrix (RoutingAlgebra.Step 𝓡𝓐) n

    open RoutingAlgebra 𝓡𝓐 public

    RTable : Set b
    RTable = Table Route n
    
    RMatrix : Set b
    RMatrix = SquareMatrix Route n

    open import RoutingLib.Data.Matrix.Relation.DecidableEquality DS public
    open import RoutingLib.Data.Table.Relation.DecidableEquality DS public

    ℝ𝕋ₛ : Setoid b ℓ
    ℝ𝕋ₛ = 𝕋ₛ n
    
    ℝ𝕄ₛ : Setoid b ℓ
    ℝ𝕄ₛ = 𝕄ₛ n n
    
    weight : SimplePath n → Route
    weight invalid                       = 0#
    weight (valid [])                    = 1#
    weight (valid ((i , j) ∷ p ∣ _ ∣ _)) = A i j ▷ weight (valid p)
    
    weight-cong : ∀ {p q : SimplePath n} → p ≈ₚ q → weight p ≈ weight q
    weight-cong invalid              = ≈-refl
    weight-cong (valid [])           = ≈-refl
    weight-cong (valid (refl ∷ p≈q)) = ▷-cong _ (weight-cong (valid p≈q))
