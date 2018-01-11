open import Algebra.FunctionProperties using (Op₂; Congruent₂)
open import Data.Fin using (Fin)
open import Data.List using (List)
import Data.List.Any.Membership as Membership
open import Data.Nat using (ℕ)
open import Data.Product using (∃; _×_; Σ)
open import Data.Maybe
open import Function.Equality using (_⟶_; Π)
open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary using (Rel; IsDecEquivalence; Setoid; DecSetoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import RoutingLib.Algebra.FunctionProperties using (_Preservesₗ_)
open import RoutingLib.Data.List.Any.Membership.Propositional using (∈-concat⁺; ∈-tabulate⁺)
open import RoutingLib.Data.List.Uniqueness using (Unique)
open import RoutingLib.Data.Matrix using (SquareMatrix; Matrix)
open import RoutingLib.Data.Graph.SimplePath using (SimplePath; []; [_]; _∺_; _∷_; _∺_∣_; _∷_∣_; source) renaming (_≈_ to _≈ₚ_)
open import RoutingLib.Data.Graph.SimplePath.Properties using (p≈q⇒p₀≡q₀)

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
      ( refl      to ≈-refl
      ; reflexive to ≈-reflexive
      ; sym       to ≈-sym
      ; trans     to ≈-trans
      ) public

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
    no-eta-equality -- Needed due to bug #2732 in Agda
    
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

    weight : SimplePath n → Route
    weight []            = 1#
    weight [ i ∺ j ∣ _ ] = A i j ▷ 1#
    weight [ i ∷ p ∣ _ ] = A i (source p) ▷ weight [ p ]

    weight-cong : ∀ {p q : SimplePath n} → p ≈ₚ q → weight p ≈ weight q
    weight-cong []              = ≈-refl
    weight-cong [ refl ∺ refl ] = ≈-refl
    weight-cong [ refl ∷ p≈q  ] rewrite p≈q⇒p₀≡q₀ p≈q =
      ▷-cong _ (weight-cong [ p≈q ])

  -----------
  -- Other --
  -----------
{-
  record HasFiniteImage {a b ℓ₁ ℓ₂} (F : Setoid a ℓ₁) (T : Setoid b ℓ₂) (fun : F ⟶ T) : Set _ where

    open Setoid F using () renaming (Carrier to A)
    open Setoid T using () renaming (Carrier to B)
    open Membership T using (_∈_)
    open Π fun using () renaming (_⟨$⟩_ to f)
    
    field
      image    : List B
      unique   : Unique T image
      complete : ∀ a → f a ∈ image
      sound    : ∀ {b} → b ∈ image → ∃ λ a → f a ≡ b
      {-
      sorted   : Sortedℕ h-image
      -}
-}
