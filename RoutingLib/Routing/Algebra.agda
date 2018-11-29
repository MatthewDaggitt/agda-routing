open import Algebra.FunctionProperties
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List)
import Data.List.Membership.Setoid as ListMembership
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_)
open import Level using (_⊔_) renaming (suc to lsuc)
open import Relation.Nullary using (¬_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Relation.Binary.Construct.NonStrictToStrict as NonStrictToStrict
import Relation.Binary.EqReasoning as EqReasoning

open import RoutingLib.Data.Matrix using (SquareMatrix)
open import RoutingLib.Data.Table using (Table)
import RoutingLib.Data.Path.UncertifiedI as UncertifiedPaths
import RoutingLib.Data.Path.CertifiedI as CertifiedPaths
import RoutingLib.Data.Matrix.Relation.DecidableEquality as MatrixDecEquality
import RoutingLib.Data.Table.Relation.DecidableEquality as TableDecEquality
import RoutingLib.Relation.Binary.Construct.NaturalOrder.Right as RightNaturalOrder

module RoutingLib.Routing.Algebra  where

--------------------------------------------------------------------------------
-- Routing algebras --
--------------------------------------------------------------------------------
-- Raw routing algebra without any properties

record RawRoutingAlgebra a b ℓ : Set (lsuc (a ⊔ b ⊔ ℓ)) where
  no-eta-equality -- Needed due to bug #2732 in Agda

  infix 4 _≈_
  infix 7 _⊕_
  infix 6 _▷_

  field
    Route            : Set b
    Step             : ∀ {n} → Fin n → Fin n → Set a
    
    _≈_              : Rel Route ℓ
    _⊕_              : Op₂ Route
    _▷_              : ∀ {n} {i j : Fin n} → Step i j → Route → Route
    0#               : Route
    ∞                : Route
    f∞               : ∀ {n} (i j : Fin n) → Step i j

    ≈-isDecEquivalence : IsDecEquivalence _≈_
    ⊕-cong             : Congruent₂ _≈_ _⊕_
    ▷-cong             : ∀ {n} {i j : Fin n} (f : Step i j) → Congruent₁ _≈_ (f ▷_)
    f∞-reject          : ∀ {n} (i j : Fin n) x → f∞ i j ▷ x ≈ ∞

  -- Publicly re-export some useful terminology
  
  open RightNaturalOrder _≈_ _⊕_ public using () renaming ( _≤_ to _≤₊_ )
  open NonStrictToStrict _≈_ _≤₊_ public using () renaming ( _<_ to _<₊_)

  infix 4 _≉_
  _≉_ : Rel Route ℓ
  x ≉ y = ¬ (x ≈ y)

  infix 4 _≰₊_
  _≰₊_ : Rel Route ℓ
  x ≰₊ y = ¬ (x ≤₊ y) 
  
  -- Publicly export equality proofs
  
  open IsDecEquivalence ≈-isDecEquivalence public
    renaming
    ( refl          to ≈-refl
    ; reflexive     to ≈-reflexive
    ; sym           to ≈-sym
    ; trans         to ≈-trans
    ; isEquivalence to ≈-isEquivalence
    ) public

  S : Setoid _ ℓ
  S = record { isEquivalence = ≈-isEquivalence }

  DS : DecSetoid _ ℓ
  DS = record { isDecEquivalence = ≈-isDecEquivalence }

--------------------------------------------------------------------------------
-- Other additional properties that a raw routing algebra may possess

module _ {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) where

  open RawRoutingAlgebra algebra
  open ListMembership S renaming (_∈_ to _∈ₗ_)

  IsDistributive : Set _
  IsDistributive = ∀ {n} {i j : Fin n} (f : Step i j) x y → f ▷ (x ⊕ y) ≈ (f ▷ x) ⊕ (f ▷ y)
  
  IsIncreasing : Set _
  IsIncreasing = ∀ {n} {i j : Fin n} (f : Step i j) x → x ≤₊ (f ▷ x)

  IsStrictlyIncreasing : Set _
  IsStrictlyIncreasing = ∀ {n} {i j : Fin n} (f : Step i j) {x} → x ≉ ∞ → x <₊ (f ▷ x)

  IsFinite : Set _
  IsFinite = Σ (List Route) (λ rs → ∀ r → r ∈ₗ rs)

--------------------------------------------------------------------------------
-- Algebras that represent distance-vector protocols

module _ {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) where

  open RawRoutingAlgebra algebra
  
  record IsRoutingAlgebra : Set (a ⊔ b ⊔ ℓ) where
    no-eta-equality -- Needed due to bug #2732 in Agda

    field
      ⊕-sel        : Selective _≈_ _⊕_
      ⊕-comm       : Commutative _≈_ _⊕_
      ⊕-assoc      : Associative _≈_ _⊕_
      ⊕-zeroʳ      : RightZero _≈_ 0# _⊕_
      ⊕-identityʳ  : RightIdentity _≈_ ∞ _⊕_
      ▷-fixedPoint : ∀ {n} {i j : Fin n} (f : Step i j) → f ▷ ∞ ≈ ∞    

--------------------------------------------------------------------------------
-- Algebras that represent path-vector protocols

module _ {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) where

  open RawRoutingAlgebra algebra
  open UncertifiedPaths
  
  record IsPathAlgebra : Set (a ⊔ b ⊔ ℓ) where
    no-eta-equality -- Needed due to bug #2732 in Agda

    field
      path           : Route → Path
      path-cong      : path Preserves _≈_ ⟶ _≡_
      r≈0⇒path[r]≈[] : ∀ {r} → r ≈ 0# → path r ≡ valid []
      r≈∞⇒path[r]≈∅  : ∀ {r} → r ≈ ∞  → path r ≡ invalid
      path[r]≈∅⇒r≈∞  : ∀ {r} → path r ≡ invalid → r ≈ ∞
      path-reject    : ∀ {n} {i j : Fin n} {r p} (f : Step i j) → path r ≡ valid p →
                       (¬ (toℕ i , toℕ j) ⇿ᵥ p) ⊎ toℕ i ∈ᵥₚ p → f ▷ r ≈ ∞
      path-accept    : ∀ {n} {i j : Fin n} {r p} (f : Step i j) → path r ≡ valid p →
                       f ▷ r ≉ ∞ → path (f ▷ r) ≡ valid ((toℕ i , toℕ j) ∷ p)

--------------------------------------------------------------------------------
-- Algebras that represent path-vector protocols with nodes in network
-- and proofs of simple paths

module _ {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) where

  open RawRoutingAlgebra algebra
  open CertifiedPaths
  
  record IsCertifiedPathAlgebra (n : ℕ) : Set (a ⊔ b ⊔ ℓ) where
    no-eta-equality -- Needed due to bug #2732 in Agda

    field
      path           : Route → Path n
      path-cong      : path Preserves _≈_ ⟶ _≈ₚ_
      r≈0⇒path[r]≈[] : ∀ {r} → r ≈ 0# → path r ≈ₚ valid []
      r≈∞⇒path[r]≈∅  : ∀ {r} → r ≈ ∞  → path r ≈ₚ invalid
      path[r]≈∅⇒r≈∞  : ∀ {r} → path r ≈ₚ invalid → r ≈ ∞
      path-reject    : ∀ {i j : Fin n} {r p} (f : Step i j) → path r ≈ₚ valid p →
                       (¬ (i , j) ⇿ᵛ p) ⊎ i ∈ᵥₚ p → f ▷ r ≈ ∞
      path-accept    : ∀ {i j : Fin n} {r p} (f : Step i j) → path r ≈ₚ valid p → f ▷ r ≉ ∞ →
                       ∀ ij⇿p i∉p → path (f ▷ r) ≈ₚ valid ((i , j) ∷ p ∣ ij⇿p ∣ i∉p)

    -- Functions

    size : Route → ℕ
    size r = length (path r)

    weight : (∀ i j → Step i j) → Path n → Route
    weight A invalid                       = ∞
    weight A (valid [])                    = 0#
    weight A (valid ((i , j) ∷ p ∣ _ ∣ _)) = A i j ▷ weight A (valid p)
