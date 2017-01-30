open import Algebra.FunctionProperties using (Op₂)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; suc)
open import Data.List using (List)
open import Data.List.All using (All; []; _∷_; all) renaming (lookup to all-lookup)
open import Data.List.Any using (satisfied)
open import Data.Product using (∃₂; _×_; _,_)
open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Rel; IsDecEquivalence; Setoid; Reflexive; Symmetric; Transitive; Decidable; IsEquivalence; _⇒_)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl; setoid to ≡-setoid)

open import RoutingLib.Algebra.FunctionProperties using (_Preserves_; _Preservesₗ_)
open import RoutingLib.Data.List using (allFin; combine)
open import RoutingLib.Data.List.Properties using ()
open import RoutingLib.Data.List.Any.PropositionalMembership using (_∈_; ∈-combine; ∈-allFin)
open import RoutingLib.Data.List.All.Properties as AllProperties using (¬All→Any¬; combine-all)

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
      0# : Route
      1# : Route

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

    open RoutingAlgebra ra public


    ---------
    -- Some useful definitions to accompany a routing problem

    Fₛ : Setoid lzero lzero
    Fₛ = ≡-setoid (Fin n)

    F×Fₛ : Setoid lzero lzero
    F×Fₛ = ≡-setoid (Fin n × Fin n)

    -- A routing matrix
    RMatrix : Set b
    RMatrix = Fin n → Fin n → Route

    -- Equality between routing matrices
    _≈ₘ_ : Rel RMatrix ℓ
    A ≈ₘ B = ∀ i j → A i j ≈ B i j

    _≉ₘ_ : Rel RMatrix ℓ
    A ≉ₘ B = ¬ (A ≈ₘ B)

    srcDstPairs : List (Fin n × Fin n)
    srcDstPairs = combine _,_ (allFin n) (allFin n)


    abstract
      
      ∈-srcDstPairs : ∀ (p : Fin n × Fin n) → p ∈ srcDstPairs
      ∈-srcDstPairs (i , j) = ∈-combine _,_ (∈-allFin i) (∈-allFin j)

      ≈ₘ-reflexive : _≡_ ⇒ _≈ₘ_
      ≈ₘ-reflexive ≡-refl i j = reflexive ≡-refl

      ≈ₘ-refl : Reflexive _≈ₘ_
      ≈ₘ-refl i j = refl

      ≈ₘ-sym : Symmetric _≈ₘ_
      ≈ₘ-sym A≈B i j = sym (A≈B i j)

      ≈ₘ-trans : Transitive _≈ₘ_
      ≈ₘ-trans A≈B B≈C i j = trans (A≈B i j) (B≈C i j)

      _≟ₘ_ : Decidable _≈ₘ_
      X ≟ₘ Y with (all (λ {(i , j) → X i j ≟ Y i j})) srcDstPairs
      ... | yes all  = yes (λ i j → all-lookup all (∈-srcDstPairs (i , j)))
      ... | no  ¬all = no (λ X≈Y → ¬all (combine-all Fₛ Fₛ _,_ (allFin n) (allFin n) (λ {x} {y} _ _ → X≈Y x y)))

      ≈ₘ-isEquivalence : IsEquivalence _≈ₘ_
      ≈ₘ-isEquivalence = record { 
          refl = ≈ₘ-refl ; 
          sym = ≈ₘ-sym ; 
          trans = ≈ₘ-trans 
        }

      ≉ₘ-witness : ∀ {X Y} → X ≉ₘ Y → ∃₂ λ i j → ¬ (X i j ≈ Y i j)
      ≉ₘ-witness {X} {Y} X≉Y with (all (λ {(i , j) → X i j ≟ Y i j})) srcDstPairs
      ... | yes all  = contradiction (λ i j → all-lookup all (∈-srcDstPairs (i , j))) X≉Y
      ... | no  ¬all with satisfied (¬All→Any¬ (λ {(i , j) → X i j ≟ Y i j}) ¬all)
      ...   | (i , j) , y = i , j , y

      

    Sₘ : Setoid b ℓ
    Sₘ = record { 
        Carrier = RMatrix ; 
       _≈_ = _≈ₘ_ ; 
       isEquivalence = ≈ₘ-isEquivalence 
      }
