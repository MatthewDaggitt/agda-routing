open import Algebra.FunctionProperties
open import Algebra.FunctionProperties.Consequences using (sel⇒idem)
open import Data.Fin using (Fin)
open import Data.List using (List)
import Data.List.Membership.Setoid as ListMembership
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Maybe
open import Data.Sum using (_⊎_)
open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Relation.Binary.EqReasoning as EqReasoning

open import RoutingLib.Data.Matrix using (SquareMatrix)
open import RoutingLib.Data.Table using (Table)
import RoutingLib.Data.Matrix.Relation.DecidableEquality as MatrixDecEquality
import RoutingLib.Data.Table.Relation.DecidableEquality as TableDecEquality
open import RoutingLib.Data.Path.Certified.FiniteEdge
  using (Path; valid; invalid; []; _∷_∣_∣_; _≈ₚ_; length)
import RoutingLib.Relation.Binary.NaturalOrder.Right as RightNaturalOrder
open import RoutingLib.Data.Path.Certified.FiniteEdge.NonEmpty using (_⇿_; _∈_)

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
    Step             : Set a
    Route            : Set b
    _≈_              : Rel Route ℓ
    _⊕_              : Op₂ Route
    _▷_              : Step → Route → Route
    0#               : Route
    ∞                : Route

    ≈-isDecEquivalence : IsDecEquivalence _≈_
    ▷-cong             : ∀ e → Congruent₁ _≈_ (e ▷_)
    ⊕-cong             : Congruent₂    _≈_ _⊕_

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
-- Routing algebras

record IsRoutingAlgebra {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) : Set (a ⊔ b ⊔ ℓ) where

  open RawRoutingAlgebra algebra

  field
    ⊕-sel       : Selective _≈_ _⊕_
    ⊕-comm      : Commutative _≈_ _⊕_
    ⊕-assoc     : Associative _≈_ _⊕_
    ⊕-zeroʳ     : RightZero _≈_ 0# _⊕_
    ⊕-identityʳ : RightIdentity _≈_ ∞ _⊕_
    ▷-zero      : ∀ (f : Step) → (f ▷ ∞) ≈ ∞

record RoutingAlgebra a b ℓ : Set (lsuc (a ⊔ b ⊔ ℓ)) where
  no-eta-equality -- Needed due to bug #2732 in Agda

  field
    rawRoutingAlgebra : RawRoutingAlgebra a b ℓ
    isRoutingAlgebra  : IsRoutingAlgebra rawRoutingAlgebra

  open RawRoutingAlgebra rawRoutingAlgebra public
  open IsRoutingAlgebra isRoutingAlgebra public

--------------------------------------------------------------------------------
-- Increasing routing algebras

record IsIncreasingRoutingAlgebra {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) : Set (a ⊔ b ⊔ ℓ)
  where

  open RawRoutingAlgebra algebra

  field
    isRoutingAlgebra : IsRoutingAlgebra algebra
    ▷-increasing     : ∀ f x → x ≤₊ (f ▷ x)

record IncreasingRoutingAlgebra a b ℓ : Set (lsuc (a ⊔ b ⊔ ℓ)) where

  field
    rawRoutingAlgebra          : RawRoutingAlgebra a b ℓ
    isIncreasingRoutingAlgebra : IsIncreasingRoutingAlgebra rawRoutingAlgebra

  open RawRoutingAlgebra rawRoutingAlgebra public
  open IsIncreasingRoutingAlgebra isIncreasingRoutingAlgebra public

  routingAlgebra : RoutingAlgebra a b ℓ
  routingAlgebra = record {isRoutingAlgebra = isRoutingAlgebra}

--------------------------------------------------------------------------------
-- Strictly increasing routing algebras

record IsStrictlyIncreasingRoutingAlgebra {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) : Set (a ⊔ b ⊔ ℓ)
  where

  open RawRoutingAlgebra algebra

  field
    isRoutingAlgebra     : IsRoutingAlgebra algebra
    ▷-strictlyIncreasing : ∀ f {x} → x ≉ ∞ → x <₊ (f ▷ x)

  open IsRoutingAlgebra isRoutingAlgebra public

  ▷-increasing : ∀ f x → x ≤₊ f ▷ x
  ▷-increasing f x with x ≟ ∞
  ... | no  x≉∞ = proj₁ (▷-strictlyIncreasing f x≉∞)
  ... | yes x≈∞ = begin
    (f ▷ x) ⊕ x ≈⟨ ⊕-cong (▷-cong f x≈∞) x≈∞ ⟩
    (f ▷ ∞) ⊕ ∞ ≈⟨ ⊕-cong (▷-zero f) ≈-refl ⟩
    ∞       ⊕ ∞ ≈⟨ sel⇒idem S ⊕-sel ∞ ⟩
    ∞           ≈⟨ ≈-sym x≈∞ ⟩
    x           ∎
    where open EqReasoning S

  isIncreasingRoutingAlgebra : IsIncreasingRoutingAlgebra algebra
  isIncreasingRoutingAlgebra = record
    { isRoutingAlgebra = isRoutingAlgebra
    ; ▷-increasing     = ▷-increasing
    }

record StrictlyIncreasingRoutingAlgebra a b ℓ : Set (lsuc (a ⊔ b ⊔ ℓ)) where

  field
    rawRoutingAlgebra                  : RawRoutingAlgebra a b ℓ
    isStrictlyIncreasingRoutingAlgebra : IsStrictlyIncreasingRoutingAlgebra rawRoutingAlgebra

  open RawRoutingAlgebra rawRoutingAlgebra public
  open IsStrictlyIncreasingRoutingAlgebra isStrictlyIncreasingRoutingAlgebra public

  routingAlgebra : RoutingAlgebra a b ℓ
  routingAlgebra = record {isRoutingAlgebra = isRoutingAlgebra}

  increasingRoutingAlgebra : IncreasingRoutingAlgebra a b ℓ
  increasingRoutingAlgebra = record
    { isIncreasingRoutingAlgebra = isIncreasingRoutingAlgebra
    }

--------------------------------------------------------------------------------
-- Finite increasing routing algebra

record IsFiniteStrictlyIncreasingRoutingAlgebra {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) : Set (a ⊔ b ⊔ ℓ)
  where

  open RawRoutingAlgebra algebra

  field
    isStrictlyIncreasingRoutingAlgebra : IsStrictlyIncreasingRoutingAlgebra algebra

  open IsStrictlyIncreasingRoutingAlgebra isStrictlyIncreasingRoutingAlgebra public
  open ListMembership S renaming (_∈_ to _∈ₗ_)

  field
    allRoutes   : List Route
    ∈-allRoutes : ∀ r → r ∈ₗ allRoutes

record FiniteStrictlyIncreasingRoutingAlgebra a b ℓ : Set (lsuc (a ⊔ b ⊔ ℓ)) where

  field
    rawRoutingAlgebra                        : RawRoutingAlgebra a b ℓ
    isFiniteStrictlyIncreasingRoutingAlgebra : IsFiniteStrictlyIncreasingRoutingAlgebra rawRoutingAlgebra

  open RawRoutingAlgebra rawRoutingAlgebra public
  open IsFiniteStrictlyIncreasingRoutingAlgebra isFiniteStrictlyIncreasingRoutingAlgebra public

  strictlyIncreasingRoutingAlgebra : StrictlyIncreasingRoutingAlgebra a b ℓ
  strictlyIncreasingRoutingAlgebra = record
    { isStrictlyIncreasingRoutingAlgebra = isStrictlyIncreasingRoutingAlgebra
    }

  open StrictlyIncreasingRoutingAlgebra strictlyIncreasingRoutingAlgebra public
    using (increasingRoutingAlgebra; routingAlgebra)


--------------------------------------------------------------------------------
-- Path algebras --
--------------------------------------------------------------------------------
-- Raw path algebras without properties

record RawPathAlgebra a b ℓ n : Set (lsuc (a ⊔ b ⊔ ℓ)) where

  field
    rawRoutingAlgebra : RawRoutingAlgebra a b ℓ

  open RawRoutingAlgebra rawRoutingAlgebra public

  field
    A        : SquareMatrix Step n
    path     : Route → Path n

--------------------------------------------------------------------------------
-- Path algebra

record IsPathAlgebra {a b ℓ n} (algebra : RawPathAlgebra a b ℓ n) : Set (a ⊔ b ⊔ ℓ) where

  open RawPathAlgebra algebra

  field
    isRoutingAlgebra : IsRoutingAlgebra rawRoutingAlgebra

    path-cong      : path Preserves _≈_ ⟶ _≈ₚ_
    r≈0⇒path[r]≈[] : ∀ {r} → r ≈ 0# → path r ≈ₚ valid []
    r≈∞⇒path[r]≈∅  : ∀ {r} → r ≈ ∞ → path r ≈ₚ invalid
    path[r]≈∅⇒r≈∞  : ∀ {r} → path r ≈ₚ invalid  → r ≈ ∞
    path-reject    : ∀ {i j r p} → path r ≈ₚ valid p → ¬ (i , j) ⇿ p ⊎ i ∈ p →
                     (A i j ▷ r) ≈ ∞
    path-accept    : ∀ {i j r p} → path r ≈ₚ valid p → ¬ ((A i j ▷ r) ≈ ∞) →
                       ∀ ij⇿p i∉p → path (A i j ▷ r) ≈ₚ valid ((i , j) ∷ p ∣ ij⇿p ∣ i∉p)

  open IsRoutingAlgebra isRoutingAlgebra public

  -- Functions

  size : Route → ℕ
  size r = length (path r)

  weight : Path n → Route
  weight invalid                       = ∞
  weight (valid [])                    = 0#
  weight (valid ((i , j) ∷ p ∣ _ ∣ _)) = A i j ▷ weight (valid p)

  -- Consistency

  𝑪 : Route → Set ℓ
  𝑪 r = weight (path r) ≈ r

  𝑰 : Route → Set ℓ
  𝑰 r = ¬ 𝑪 r

record PathAlgebra a b ℓ n : Set (lsuc (a ⊔ b ⊔ ℓ)) where

  field
    rawPathAlgebra : RawPathAlgebra a b ℓ n
    isPathAlgebra  : IsPathAlgebra rawPathAlgebra

  open RawPathAlgebra rawPathAlgebra public
  open IsPathAlgebra isPathAlgebra public

  routingAlgebra : RoutingAlgebra a b ℓ
  routingAlgebra = record
    { isRoutingAlgebra = isRoutingAlgebra
    }

--------------------------------------------------------------------------------
-- Increasing path algebra

record IsIncreasingPathAlgebra {a b ℓ n} (algebra : RawPathAlgebra a b ℓ n) : Set (a ⊔ b ⊔ ℓ)
  where

  open RawPathAlgebra algebra

  field
    isPathAlgebra : IsPathAlgebra algebra
    ▷-increasing : ∀ f x → x ≤₊ (f ▷ x)

  open IsPathAlgebra isPathAlgebra public

record IncreasingPathAlgebra a b ℓ n : Set (lsuc (a ⊔ b ⊔ ℓ)) where

  field
    rawPathAlgebra          : RawPathAlgebra a b ℓ n
    isIncreasingPathAlgebra : IsIncreasingPathAlgebra rawPathAlgebra

  open RawPathAlgebra rawPathAlgebra public
  open IsIncreasingPathAlgebra isIncreasingPathAlgebra public

  pathAlgebra : PathAlgebra a b ℓ n
  pathAlgebra = record
    { isPathAlgebra = isPathAlgebra
    }

  open PathAlgebra pathAlgebra public
    using (routingAlgebra)

--------------------------------------------------------------------------------
-- Strictly increasing path algebra

record IsStrictlyIncreasingPathAlgebra
  {a b ℓ n} (algebra : RawPathAlgebra a b ℓ n) : Set (a ⊔ b ⊔ ℓ)
  where

  open RawPathAlgebra algebra

  field
    isPathAlgebra : IsPathAlgebra algebra
    ▷-strictlyIncreasing : ∀ f {x} → x ≉ ∞ → x <₊ (f ▷ x)

  open IsPathAlgebra isPathAlgebra public

  ▷-increasing : ∀ f x → x ≤₊ f ▷ x
  ▷-increasing f x with x ≟ ∞
  ... | no  x≉∞ = proj₁ (▷-strictlyIncreasing f x≉∞)
  ... | yes x≈∞ = begin
    (f ▷ x) ⊕ x ≈⟨ ⊕-cong (▷-cong f x≈∞) x≈∞ ⟩
    (f ▷ ∞) ⊕ ∞ ≈⟨ ⊕-cong (▷-zero f) ≈-refl ⟩
    ∞       ⊕ ∞ ≈⟨ sel⇒idem S ⊕-sel ∞ ⟩
    ∞           ≈⟨ ≈-sym x≈∞ ⟩
    x           ∎
    where open EqReasoning S

  isIncreasingPathAlgebra : IsIncreasingPathAlgebra algebra
  isIncreasingPathAlgebra = record
    { isPathAlgebra = isPathAlgebra
    ; ▷-increasing     = ▷-increasing
    }

record StrictlyIncreasingPathAlgebra a b ℓ n : Set (lsuc (a ⊔ b ⊔ ℓ)) where

  field
    rawPathAlgebra                  : RawPathAlgebra a b ℓ n
    isStrictlyIncreasingPathAlgebra : IsStrictlyIncreasingPathAlgebra rawPathAlgebra

  open RawPathAlgebra rawPathAlgebra public
  open IsStrictlyIncreasingPathAlgebra isStrictlyIncreasingPathAlgebra public

  increasingPathAlgebra : IncreasingPathAlgebra a b ℓ n
  increasingPathAlgebra = record
    { isIncreasingPathAlgebra = isIncreasingPathAlgebra
    }

  open IncreasingPathAlgebra increasingPathAlgebra public
    using (pathAlgebra; routingAlgebra)
