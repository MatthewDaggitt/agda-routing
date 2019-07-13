--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module contains the core definitions for routing algebras and some
-- simple associated properties. A routing algebra is an abstract representation
-- of some problem that we want our routing protocol to solve (e.g. the
-- shortest paths problem, the widest paths problem).
--------------------------------------------------------------------------------

module RoutingLib.Routing.Algebra  where

open import Algebra
open import Algebra.Structures
open import Algebra.FunctionProperties
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List)
import Data.List.Membership.Setoid as ListMembership
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_)
open import Level using (Lift; lift; _⊔_) renaming (suc to lsuc)
open import Function using (_∘_)
open import Relation.Nullary using (¬_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
import Relation.Binary.Construct.NonStrictToStrict as NonStrictToStrict
import Relation.Binary.Construct.NaturalOrder.Right as RightNaturalOrder
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import RoutingLib.Algebra
open import RoutingLib.Algebra.Structures
open import RoutingLib.Data.Matrix using (SquareMatrix)
open import RoutingLib.Data.Table using (Table)
import RoutingLib.Data.Path.UncertifiedI as UncertifiedPaths
import RoutingLib.Data.Path.CertifiedI as CertifiedPaths
open import RoutingLib.Data.Path.UncertifiedI.Properties
import RoutingLib.Data.Matrix.Relation.Binary.DecidableEquality as MatrixDecEquality
import RoutingLib.Data.Table.Relation.Binary.DecidableEquality as TableDecEquality

--------------------------------------------------------------------------------
-- Raw routing algebras --
--------------------------------------------------------------------------------
-- This definition defines the structure of a routing algebra. In this record
-- the algebra is not assumed to have any of the natural properties we would
-- expect, only that the operations respect the associated notion of equality
-- over routes.
--
-- These raw structures are useful when one algebra that may
-- not technically be a routing algebra but still simulates a true routing
-- algebra. 

record RawRoutingAlgebra a b ℓ : Set (lsuc (a ⊔ b ⊔ ℓ)) where
  no-eta-equality -- Needed due to bug #2732 in Agda

  infix 4 _≈_
  infix 7 _⊕_
  infix 6 _▷_

  field
    -- The type of the routes
    Route            : Set a
    -- The type of edge labels for each arc (i , j)
    Step             : ∀ {n} → Fin n → Fin n → Set b

    -- Equality between routes
    _≈_              : Rel Route ℓ
    -- Operation for choosing between routes
    _⊕_              : Op₂ Route
    -- Operation for extending a route along an edge
    _▷_              : ∀ {n} {i j : Fin n} → Step i j → Route → Route
    -- The trivial route
    0#               : Route
    -- The invalid route
    ∞#               : Route
    -- The invalid edge weight
    f∞               : ∀ {n} (i j : Fin n) → Step i j

    -- The _≈_ relation really is an equality relation
    ≈-isDecEquivalence : IsDecEquivalence _≈_
    ⊕-cong             : Congruent₂ _≈_ _⊕_
    ▷-cong             : ∀ {n} {i j : Fin n} (f : Step i j) → Congruent₁ _≈_ (f ▷_)

    -- The invalid edge weight really does reject routes
    f∞-reject          : ∀ {n} (i j : Fin n) x → f∞ i j ▷ x ≈ ∞#


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

  -- Publicly re-export some useful terminology
  open RightNaturalOrder _≈_ _⊕_ public using () renaming (_≤_ to _≤₊_)
  open NonStrictToStrict _≈_ _≤₊_ public using () renaming (_<_ to _<₊_)

  infix 4 _≉_ _≤₊?_ _<₊?_ _≮₊_ _≰₊_
  
  _≉_ : Rel Route ℓ
  x ≉ y = ¬ (x ≈ y)

  _≮₊_ : Rel Route ℓ
  x ≮₊ y = ¬ (x <₊ y)

  _≰₊_ : Rel Route ℓ
  x ≰₊ y = ¬ (x ≤₊ y)

  _≤₊?_ : Decidable _≤₊_
  x ≤₊? y = x ≟ y ⊕ x
  
  _<₊?_ : Decidable _<₊_
  _<₊?_ = NonStrictToStrict.<-decidable _≈_ _≤₊_ _≟_ _≤₊?_

  ⊕-isMagma : IsMagma _≈_ _⊕_
  ⊕-isMagma = record
    { isEquivalence = ≈-isEquivalence
    ; ∙-cong        = ⊕-cong
    }

  ⊕-magma : Magma _ _
  ⊕-magma = record
    { isMagma = ⊕-isMagma
    }

  ⊕-isDecMagma : IsDecMagma _≈_ _⊕_
  ⊕-isDecMagma = record
    { isMagma = ⊕-isMagma
    ; _≟_     = _≟_
    }

  ⊕-decMagma : DecMagma _ _
  ⊕-decMagma = record
    { isDecMagma = ⊕-isDecMagma
    }

  open Magma ⊕-magma public using ()
    renaming
    ( ∙-congˡ to ⊕-congˡ
    ; ∙-congʳ to ⊕-congʳ
    )

  ≤₊-respʳ-≈ : _≤₊_ Respectsʳ _≈_
  ≤₊-respʳ-≈ = RightNaturalOrder.respʳ _≈_  _⊕_ ⊕-isMagma  

  ≤₊-respˡ-≈ : _≤₊_ Respectsˡ _≈_
  ≤₊-respˡ-≈ = RightNaturalOrder.respˡ _≈_  _⊕_ ⊕-isMagma

--------------------------------------------------------------------------------
-- Basic properties
--------------------------------------------------------------------------------
-- Basic important properties an algebra may possess

module _ {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) where

  open RawRoutingAlgebra algebra
  open ListMembership S renaming (_∈_ to _∈ₗ_)

  -- Distributivity = you and your neighbour's choices always agree
  IsDistributive : Set _
  IsDistributive = ∀ {n} {i j : Fin n} (f : Step i j) x y → f ▷ (x ⊕ y) ≈ (f ▷ x) ⊕ (f ▷ y)
  
  -- Increasing = extending a route never makes it better
  IsIncreasing : Set _
  IsIncreasing = ∀ {n} {i j : Fin n} (f : Step i j) x → x ≤₊ (f ▷ x)

  -- Strictly increasing = extending a route always makes it worse
  IsStrictlyIncreasing : Set _
  IsStrictlyIncreasing = ∀ {n} {i j : Fin n} (f : Step i j) {x} → x ≉ ∞# → x <₊ (f ▷ x)

  -- Finite = there only exist a finite number of weights
  IsFinite : Set _
  IsFinite = Σ (List Route) (λ rs → ∀ r → r ∈ₗ rs)

  Level_DistributiveIn[_,_] : ℕ → Route → Route → Set _
  Level 0       DistributiveIn[ ⊥ , ⊤ ] =
    ∀ {n} {i j : Fin n} (f : Step i j) →
    ∀ {x y} → ⊥ ≤₊ x → x ≤₊ ⊤ → ⊥ ≤₊ y → y ≤₊ ⊤ →
    f ▷ (x ⊕ y) ≈ (f ▷ x) ⊕ (f ▷ y) 
  Level (suc k) DistributiveIn[ ⊥ , ⊤ ] =
    ∀ {n} {i j : Fin n} (f : Step i j) →
    ∀ {x y} → ⊥ ≤₊ x → x ≤₊ ⊤ → ⊥ ≤₊ y → y ≤₊ ⊤ →
    Level k DistributiveIn[ f ▷ (x ⊕ y) , (f ▷ x) ⊕ (f ▷ y) ]

  IsLevel_Distributive : ℕ → Set _
  IsLevel k Distributive = Level k DistributiveIn[ 0# , ∞# ]

  Level_DistributiveIn[_,_]Alt : ℕ → Route → Route → Set _
  Level 0       DistributiveIn[ ⊥ , ⊤ ]Alt = Lift (a ⊔ b ⊔ ℓ) (⊥ ≈ ⊤)
  Level (suc k) DistributiveIn[ ⊥ , ⊤ ]Alt =
    ∀ {n} {i j : Fin n} (f : Step i j) →
    ∀ {x y} → ⊥ ≤₊ x → x ≤₊ ⊤ → ⊥ ≤₊ y → y ≤₊ ⊤ →
    Level k DistributiveIn[ f ▷ (x ⊕ y) , (f ▷ x) ⊕ (f ▷ y) ]Alt

  IsLevel_DistributiveAlt : ℕ → Set _
  IsLevel k DistributiveAlt = Level k DistributiveIn[ 0# , ∞# ]Alt
  
--------------------------------------------------------------------------------
-- Routing algebras
--------------------------------------------------------------------------------
-- This record ensures that the corresponding raw routing algebra obeys all the
-- properties we would expect of a routing algebra. See below for descriptions.

  record IsRoutingAlgebra : Set (a ⊔ b ⊔ ℓ) where
    no-eta-equality -- Needed due to bug #2732 in Agda

    field
      -- The choice operator always returns one of its two arguments
      ⊕-sel        : Selective _≈_ _⊕_
      -- Choosing between x and y is the same as choosing between y and x
      ⊕-comm       : Commutative _≈_ _⊕_
      -- Choosing between x and y then z is the same as y and z then x
      ⊕-assoc      : Associative _≈_ _⊕_
      -- The trivial route 0# is always chosen over any other route
      ⊕-zeroʳ      : RightZero _≈_ 0# _⊕_
      -- Any route is always chosen over the invalid route ∞#
      ⊕-identityʳ  : RightIdentity _≈_ ∞# _⊕_
      -- When you extend the invalid route, the result is always invalid
      ▷-fixedPoint : ∀ {n} {i j : Fin n} (f : Step i j) → f ▷ ∞# ≈ ∞#

--------------------------------------------------------------------------------
-- Path algebras
--------------------------------------------------------------------------------
-- This encapsulates the notion that the algebra is also a path algebra. Note
-- that it does not require the algebra to divulge how paths are implemented
-- only that there exists a `path` function that obeys the natural properties.

module _ {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) where

  open RawRoutingAlgebra algebra
  open UncertifiedPaths

  record IsPathAlgebra : Set (a ⊔ b ⊔ ℓ) where
    no-eta-equality -- Needed due to bug #2732 in Agda

    field
      -- Every route has an associated path
      path           : Route → Path
      -- The paths of two equal routes are equal
      path-cong      : path Preserves _≈_ ⟶ _≡_
      -- The path of the trivial route is the empty path
      r≈0⇒path[r]≈[] : ∀ {r} → r ≈ 0# → path r ≡ valid []
      -- The path of the invalid route is the invalid path
      r≈∞⇒path[r]≈∅  : ∀ {r} → r ≈ ∞#  → path r ≡ invalid
      -- The invalid path is only associated with the invalid route
      path[r]≈∅⇒r≈∞  : ∀ {r} → path r ≡ invalid → r ≈ ∞#
      -- The extension of a route along an edge that either doesn't match up
      -- with the start of its path (⇿) or would form a loop (i ∈ p) is always
      -- the invalid route.
      path-reject    : ∀ {n} {i j : Fin n} {r p} (f : Step i j) → path r ≡ valid p →
                       (¬ (toℕ i , toℕ j) ⇿ᵥ p) ⊎ toℕ i ∈ᵥₚ p → f ▷ r ≈ ∞#
      -- The extension of a route along a valid edge always actually adds that
      -- edge to the path.
      path-accept    : ∀ {n} {i j : Fin n} {r p} (f : Step i j) → path r ≡ valid p →
                       f ▷ r ≉ ∞# → path (f ▷ r) ≡ valid ((toℕ i , toℕ j) ∷ p)

--------------------------------------------------------------------------------
-- Certified path algebras
--------------------------------------------------------------------------------
-- This is an alternative more convenient internal representation of a path
-- algebra used by the various proofs in the library. The difference is that
-- in a certified path algebra the paths themselves contain proofs that they
-- are indeed simple paths and that all nodes in the path are truely node in the
-- network.
--
-- As shown in `RoutingLib.Routing.Algebra.Certification` the two definitions
-- may be moved between interchangably. This handled internally by the library
-- and therefore users should not need to IsCertifiedPathAlgebra themselves.

module _ {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) where

  open RawRoutingAlgebra algebra
  open CertifiedPaths

  record IsCertifiedPathAlgebra (n : ℕ) : Set (a ⊔ b ⊔ ℓ) where
    no-eta-equality -- Needed due to bug #2732 in Agda

    field
      path           : Route → Path n
      path-cong      : path Preserves _≈_ ⟶ _≈ₚ_
      r≈0⇒path[r]≈[] : ∀ {r} → r ≈ 0# → path r ≈ₚ valid []
      r≈∞⇒path[r]≈∅  : ∀ {r} → r ≈ ∞#  → path r ≈ₚ invalid
      path[r]≈∅⇒r≈∞  : ∀ {r} → path r ≈ₚ invalid → r ≈ ∞#
      path-reject    : ∀ {i j : Fin n} {r p} (f : Step i j) → path r ≈ₚ valid p →
                       (¬ (i , j) ⇿ᵛ p) ⊎ i ∈ᵥₚ p → f ▷ r ≈ ∞#
      path-accept    : ∀ {i j : Fin n} {r p} (f : Step i j) → path r ≈ₚ valid p → f ▷ r ≉ ∞# →
                       ∀ ij⇿p i∉p → path (f ▷ r) ≈ₚ valid ((i , j) ∷ p ∣ ij⇿p ∣ i∉p)

    -- Functions

    size : Route → ℕ
    size r = length (path r)

    weight : (∀ i j → Step i j) → Path n → Route
    weight A invalid                       = ∞#
    weight A (valid [])                    = 0#
    weight A (valid ((i , j) ∷ p ∣ _ ∣ _)) = A i j ▷ weight A (valid p)



module PathDistributivity
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isPathAlgebra : IsPathAlgebra algebra)
  where

  open RawRoutingAlgebra algebra
  open IsPathAlgebra isPathAlgebra
  open UncertifiedPaths

  PathDistributive : Set _
  PathDistributive = ∀ {n} {i j : Fin n} (f : Step i j) →
                     ∀ {x y} → toℕ i ∉ₚ path x → toℕ i ∉ₚ path y → f ▷ (x ⊕ y) ≈ (f ▷ x) ⊕ (f ▷ y)


  IsLevel_PathDistributiveIn[_,_]Alt : ℕ → Route → Route → Set _
  IsLevel 0       PathDistributiveIn[ ⊥ , ⊤ ]Alt = Lift (a ⊔ b ⊔ ℓ) (⊥ ≈ ⊤)
  IsLevel (suc k) PathDistributiveIn[ ⊥ , ⊤ ]Alt =
    ∀ {n} {i j : Fin n} (f : Step i j) →
    ∀ {x y} → ⊥ ≤₊ x → x ≤₊ ⊤ → ⊥ ≤₊ y → y ≤₊ ⊤ →
    toℕ i ∉ₚ path x → toℕ i ∉ₚ path y →
    (toℕ i , toℕ j) ⇿ path x → (toℕ i , toℕ j) ⇿ path y →
    IsLevel k PathDistributiveIn[ f ▷ (x ⊕ y) , (f ▷ x) ⊕ (f ▷ y) ]Alt


  -- kᵗʰ level distributivity
  IsLevel_PathDistributiveIn[_,_] : ℕ → Route → Route → Set _
  IsLevel 0       PathDistributiveIn[ ⊥ , ⊤ ] =
    ∀ {n} {i j : Fin n} (f : Step i j) →
    ∀ {x y} → ⊥ ≤₊ x → x ≤₊ ⊤ → ⊥ ≤₊ y → y ≤₊ ⊤ →
    toℕ i ∉ₚ path x → toℕ i ∉ₚ path y →
    (toℕ i , toℕ j) ⇿ path x → (toℕ i , toℕ j) ⇿ path y →
    f ▷ (x ⊕ y) ≈ (f ▷ x) ⊕ (f ▷ y) 
  IsLevel (suc k) PathDistributiveIn[ ⊥ , ⊤ ] =
    ∀ {n} {i j : Fin n} (f : Step i j) →
    ∀ {x y} → ⊥ ≤₊ x → x ≤₊ ⊤ → ⊥ ≤₊ y → y ≤₊ ⊤ →
    toℕ i ∉ₚ path x → toℕ i ∉ₚ path y →
    IsLevel k PathDistributiveIn[ f ▷ (x ⊕ y) , (f ▷ x) ⊕ (f ▷ y) ]
  
  IsLevel_PathDistributive : ℕ → Set _
  IsLevel k PathDistributive = IsLevel k PathDistributiveIn[ 0# , ∞# ]
