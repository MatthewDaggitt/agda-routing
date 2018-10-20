open import Algebra.FunctionProperties
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List)
import Data.List.Membership.Setoid as ListMembership
open import Data.Nat using (ℕ)
open import Data.Product using (Σ)
open import Level using (_⊔_) renaming (suc to lsuc)
open import Relation.Nullary using (¬_)
open import Relation.Binary using (Rel; IsDecEquivalence; Setoid; DecSetoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Relation.Binary.EqReasoning as EqReasoning

open import RoutingLib.Data.Matrix using (SquareMatrix)
open import RoutingLib.Data.Table using (Table)
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
    Step             : ∀ {n} → Fin n → Fin n → Set a
    Route            : Set b
    
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


  infix 4 _≉_
  _≉_ : Rel Route ℓ
  x ≉ y = ¬ (x ≈ y)

  open RightNaturalOrder _≈_ _⊕_ public
    using () renaming
    ( _≤_ to _≤₊_
    ; _≰_ to _≰₊_
    ; _<_ to _<₊_
    )

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
-- Other (non-standard) additional properties raw routing algebras may have

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
