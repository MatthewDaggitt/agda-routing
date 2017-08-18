open import Algebra.FunctionProperties using (Op₂; Congruent₂)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Dec using (all?; ¬∀⟶∃¬)
open import Data.Nat using (ℕ; suc)
open import Data.List using (List; concat; tabulate; allFin)
open import Data.List.All using (All; []; _∷_; all) renaming (lookup to all-lookup)
open import Data.List.Any using (Any)
open import Data.List.Any.Membership.Propositional using (_∈_)
open import Data.Product using (∃; ∃₂; _×_; _,_)
open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Rel; IsDecEquivalence; Setoid; Reflexive; Symmetric; Transitive; Decidable; DecSetoid; IsEquivalence; _⇒_)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl; setoid to ≡-setoid)

open import RoutingLib.Algebra.FunctionProperties using (_Preservesₗ_)
open import RoutingLib.Data.List using (combine)
open import RoutingLib.Data.List.All using (All₂; []; _∷_)
open import RoutingLib.Data.List.Any using (Any₂; here; there)
open import RoutingLib.Data.List.Any.Membership.Propositional using (∈-concat⁺; ∈-tabulate⁺)
open import RoutingLib.Data.Matrix using (SquareMatrix; Matrix)

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
      _⊕_   : Op₂ Route
      _▷_   : Step → Route → Route
      0#    : Route
      1#    : Route

      _≈_                : Rel Route ℓ
      ≈-isDecEquivalence : IsDecEquivalence _≈_
      ⊕-cong             : Congruent₂ _≈_ _⊕_
      ▷-cong             : _▷_ Preservesₗ _≈_
      0≉1                : ¬ (0# ≈ 1#)
      
    -- A few useful consequences of equality to export
    _≉_ : Rel Route ℓ
    x ≉ y = ¬ (x ≈ y)

    open IsDecEquivalence ≈-isDecEquivalence public

    S : Setoid b ℓ
    S = record 
      { _≈_           = _≈_
      ; isEquivalence = isEquivalence
      }

    DS : DecSetoid b ℓ
    DS = record 
      { Carrier = Route 
      ; _≈_ = _≈_ 
      ; isDecEquivalence = ≈-isDecEquivalence 
      }



  ---------------------
  -- Routing problem --
  ---------------------
  -- An instantiation of a specific routing problem for a routing algebra
  -- In particular we need an adjacency matrix (representing the topology)

  record RoutingProblem {a b ℓ} (𝓡𝓐 : RoutingAlgebra a b ℓ) (n : ℕ) : Set (lsuc (a ⊔ b ⊔ ℓ)) where
    field
      A  : SquareMatrix (RoutingAlgebra.Step 𝓡𝓐) n

    open RoutingAlgebra 𝓡𝓐 public

    RMatrix : Set b
    RMatrix = SquareMatrix Route n

    open import RoutingLib.Data.Matrix.Relation.DecidableEquality DS public
    open import RoutingLib.Data.Table.Relation.DecidableEquality DS using (𝕋ₛ)

    ℝ𝕋ₛ : Setoid b ℓ
    ℝ𝕋ₛ = 𝕋ₛ n
    
    ℝ𝕄ₛ : Setoid b ℓ
    ℝ𝕄ₛ = 𝕄ₛ n n
