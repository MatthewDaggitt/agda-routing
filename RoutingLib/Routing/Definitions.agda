open import Algebra.FunctionProperties using (Op₂; Congruent₂)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Dec using (all?)
open import Data.Nat using (ℕ; suc)
open import Data.List using (List)
open import Data.List.All using (All; []; _∷_; all) renaming (lookup to all-lookup)
open import Data.List.Any using (satisfied)
open import Data.Product using (∃₂; _×_; _,_)
open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Rel; IsDecEquivalence; Setoid; Reflexive; Symmetric; Transitive; Decidable; DecSetoid; IsEquivalence; _⇒_)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl; setoid to ≡-setoid)

open import RoutingLib.Algebra.FunctionProperties using (_Preservesₗ_)
open import RoutingLib.Data.List using (allFin; combine)
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
      ⊕-pres-≈ : Congruent₂ _≈_ _⊕_
      ▷-pres-≈ : _▷_ Preservesₗ _≈_

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
  -- and an identity matrix

  record RoutingProblem a b ℓ (n : ℕ) : Set (lsuc (a ⊔ b ⊔ ℓ)) where

    field
      ra : RoutingAlgebra a b ℓ
      A : Fin n → Fin n → RoutingAlgebra.Step ra

    open RoutingAlgebra ra public


    -------------------------------------------
    -- Setoids over nodes and pairs of nodes --
    -------------------------------------------

    Fₛ : Setoid lzero lzero
    Fₛ = ≡-setoid (Fin n)

    F×Fₛ : Setoid lzero lzero
    F×Fₛ = ≡-setoid (Fin n × Fin n)

    --------------------
    -- Routing tables --
    --------------------
  
    RTable : Set b
    RTable = Fin n → Route

    _≈ₜ_ : Rel RTable ℓ
    A ≈ₜ B = ∀ i → A i ≈ B i

    abstract

      ≈ₜ-reflexive : _≡_ ⇒ _≈ₜ_
      ≈ₜ-reflexive ≡-refl i = reflexive ≡-refl

      ≈ₜ-refl : Reflexive _≈ₜ_
      ≈ₜ-refl i = refl

      ≈ₜ-sym : Symmetric _≈ₜ_
      ≈ₜ-sym A≈B i = sym (A≈B i)

      ≈ₜ-trans : Transitive _≈ₜ_
      ≈ₜ-trans A≈B B≈C i = trans (A≈B i) (B≈C i)

      _≟ₜ_ : Decidable _≈ₜ_
      X ≟ₜ Y = all? (λ i → X i ≟ Y i)
        
      ≈ₜ-isEquivalence : IsEquivalence _≈ₜ_
      ≈ₜ-isEquivalence = record { refl = ≈ₜ-refl ; sym = ≈ₜ-sym ; trans = ≈ₜ-trans }
  
      ≈ₜ-isDecEquivalence : IsDecEquivalence _≈ₜ_
      ≈ₜ-isDecEquivalence = record { isEquivalence = ≈ₜ-isEquivalence ; _≟_ = _≟ₜ_ }
  
    Sₜ : Setoid b ℓ
    Sₜ = record { Carrier = RTable ; _≈_ = _≈ₜ_ ; isEquivalence = ≈ₜ-isEquivalence }

    DSₜ : DecSetoid b ℓ
    DSₜ = record { Carrier = RTable ; _≈_ = _≈ₜ_ ; isDecEquivalence = ≈ₜ-isDecEquivalence }


    ----------------------
    -- Routing matrices --
    ----------------------

    -- A routing matrix
    RMatrix : Set b
    RMatrix = Fin n → RTable

    -- Equality between routing matrices
    _≈ₘ_ : Rel RMatrix ℓ
    A ≈ₘ B = ∀ i j → A i j ≈ B i j

    _≉ₘ_ : Rel RMatrix ℓ
    A ≉ₘ B = ¬ (A ≈ₘ B)

    ≈ₘ-reflexive : _≡_ ⇒ _≈ₘ_
    ≈ₘ-reflexive ≡-refl i j = reflexive ≡-refl

    ≈ₘ-refl : Reflexive _≈ₘ_
    ≈ₘ-refl i j = refl

    ≈ₘ-sym : Symmetric _≈ₘ_
    ≈ₘ-sym A≈B i j = sym (A≈B i j)

    ≈ₘ-trans : Transitive _≈ₘ_
    ≈ₘ-trans A≈B B≈C i j = trans (A≈B i j) (B≈C i j)

    _≟ₘ_ : Decidable _≈ₘ_
    X ≟ₘ Y = all? (λ i  → X i ≟ₜ Y i)

    ≈ₘ-isEquivalence : IsEquivalence _≈ₘ_
    ≈ₘ-isEquivalence = record {
        refl = ≈ₘ-refl ;
        sym = ≈ₘ-sym ;
        trans = ≈ₘ-trans
      }
{-
      ≉ₘ-witness : ∀ {X Y} → X ≉ₘ Y → ∃₂ λ i j → ¬ (X i j ≈ Y i j)
      ≉ₘ-witness {X} {Y} X≉Y with (all (λ {(i , j) → X i j ≟ Y i j})) srcDstPairs
      ... | yes all  = contradiction (λ i j → all-lookup all (∈-srcDstPairs (i , j))) X≉Y
      ... | no  ¬all with satisfied (¬All→Any¬ (λ {(i , j) → X i j ≟ Y i j}) ¬all)
      ...   | (i , j) , y = i , j , y
-}


    Sₘ : Setoid b ℓ
    Sₘ = record {
        Carrier = RMatrix ;
       _≈_ = _≈ₘ_ ;
       isEquivalence = ≈ₘ-isEquivalence
      }

  
    ----------------------
    -- Routing matrices --
    ----------------------

    srcDstPairs : List (Fin n × Fin n)
    srcDstPairs = combine _,_ (allFin n) (allFin n)

    abstract

      
      ∈-srcDstPairs : ∀ (p : Fin n × Fin n) → p ∈ srcDstPairs
      ∈-srcDstPairs (i , j) = ∈-combine _,_ (∈-allFin i) (∈-allFin j)
