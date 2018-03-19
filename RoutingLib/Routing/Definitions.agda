open import Algebra.FunctionProperties using (Op₂; Congruent₂; Congruent₁)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_)
open import Data.Maybe
open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary using (Rel; IsDecEquivalence; Setoid; DecSetoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import RoutingLib.Data.Matrix using (SquareMatrix)
open import RoutingLib.Data.Table using (Table)
import RoutingLib.Data.Matrix.Relation.DecidableEquality as MatrixDecEquality
import RoutingLib.Data.Table.Relation.DecidableEquality as TableDecEquality
open import RoutingLib.Data.SimplePath
  using (SimplePath; valid; invalid; []; _∷_∣_∣_)
open import RoutingLib.Data.SimplePath.Relation.Equality
import RoutingLib.Relation.Binary.NaturalOrder.Right as RightNaturalOrder

module RoutingLib.Routing.Definitions where

  ---------------------
  -- Routing algebra --
  ---------------------
  -- A routing algebra represents the underlying algebra
  -- for a set of routing problems.

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
      ▷-cong             : ∀ e → Congruent₁ _≈_ (e ▷_)

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
    S = record { isEquivalence = ≈-isEquivalence }

    DS : DecSetoid b ℓ
    DS = record { isDecEquivalence = ≈-isDecEquivalence }    
    
    open RightNaturalOrder _≈_ _⊕_ public
      using () renaming
      ( _≤_ to _≤₊_
      ; _≰_ to _≰₊_
      ; _<_ to _<₊_
      )
      
    
  
  ---------------------
  -- Routing problem --
  ---------------------
  -- An instantiation of a specific routing problem for a routing algebra
  -- In particular we need an adjacency matrix (representing the topology)

  record RoutingProblem
    {a b ℓ} (𝓡𝓐 : RoutingAlgebra a b ℓ) (n-1 : ℕ)
    : Set (lsuc (a ⊔ b ⊔ ℓ)) where
    no-eta-equality -- Needed due to bug #2732 in Agda
    
    field
      A  : SquareMatrix (RoutingAlgebra.Step 𝓡𝓐) (suc n-1)

    n : ℕ
    n = suc n-1
    
    Node : Set
    Node = Fin n

    Edge : Set
    Edge = Fin n × Fin n
    
    open RoutingAlgebra 𝓡𝓐 public
    open MatrixDecEquality DS public
    open TableDecEquality DS using (𝕋ₛ)

    RTable : Set b
    RTable = Table Route n
    
    RMatrix : Set b
    RMatrix = SquareMatrix Route n

    ℝ𝕋ₛ : Setoid b ℓ
    ℝ𝕋ₛ = 𝕋ₛ n
    
    ℝ𝕄ₛ : Setoid b ℓ
    ℝ𝕄ₛ = 𝕄ₛ n n

    Decℝ𝕄ₛ : DecSetoid b ℓ
    Decℝ𝕄ₛ = Dec𝕄ₛ n n
    
    weight : SimplePath n → Route
    weight invalid                       = 0#
    weight (valid [])                    = 1#
    weight (valid ((i , j) ∷ p ∣ _ ∣ _)) = A i j ▷ weight (valid p)
    
    weight-cong : ∀ {p q : SimplePath n} → p ≈ₚ q → weight p ≈ weight q
    weight-cong invalid              = ≈-refl
    weight-cong (valid [])           = ≈-refl
    weight-cong (valid (refl ∷ p≈q)) = ▷-cong _ (weight-cong (valid p≈q))
