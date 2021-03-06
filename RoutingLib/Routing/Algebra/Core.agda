--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module contains the core definition of a routing algebras.
-- A routing algebra is an abstract representation of some problem that we want
-- our routing protocol to solve (e.g. the shortest paths problem, the widest
-- paths problem).
--------------------------------------------------------------------------------

module RoutingLib.Routing.Algebra.Core where

open import Algebra
open import Data.Fin using (Fin)
open import Level using (_⊔_; suc)
open import Function using (_∘_)
open import Relation.Nullary using (¬_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
import Relation.Binary.Construct.NonStrictToStrict as NonStrictToStrict
import Relation.Binary.Construct.NaturalOrder.Right as RightNaturalOrder

open import RoutingLib.Routing.Basics.Node

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

record RawRoutingAlgebra a b ℓ : Set (suc (a ⊔ b ⊔ ℓ)) where
  no-eta-equality -- Needed due to bug #2732 in Agda

  infix 4 _≈_
  infix 7 _⊕_
  infix 6 _▷_

  field
    -- The type of the routes
    PathWeight       : Set a
    -- The type of edge labels for each arc (i , j)
    Step             : ∀ {n} → Node n → Node n → Set b

    -- Equality between path-weights
    _≈_              : Rel PathWeight ℓ
    -- Operation for choosing between path-weights
    _⊕_              : Op₂ PathWeight
    -- Operation for calculating a new path-weight along an edge
    _▷_              : ∀ {n} {i j : Node n} → Step i j → PathWeight → PathWeight
    -- The trivial path weight
    0#               : PathWeight
    -- The invalid path weight
    ∞#               : PathWeight
    -- The invalid edge weight
    f∞               : ∀ {n} (i j : Node n) → Step i j

    -- The _≈_ relation is an equality relation
    ≈-isDecEquivalence : IsDecEquivalence _≈_
    ⊕-cong             : Congruent₂ _≈_ _⊕_
    ▷-cong             : ∀ {n} {i j : Node n} (f : Step i j) → Congruent₁ _≈_ (f ▷_)

    -- The invalid edge weight really does reject path-weights
    f∞-reject          : ∀ {n} (i j : Node n) x → f∞ i j ▷ x ≈ ∞#


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
  
  _≉_ : Rel PathWeight ℓ
  x ≉ y = ¬ (x ≈ y)

  _≮₊_ : Rel PathWeight ℓ
  x ≮₊ y = ¬ (x <₊ y)

  _≰₊_ : Rel PathWeight ℓ
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

  open Magma ⊕-magma public using ()
    renaming
    ( ∙-congˡ to ⊕-congˡ
    ; ∙-congʳ to ⊕-congʳ
    )

  ≤₊-respʳ-≈ : _≤₊_ Respectsʳ _≈_
  ≤₊-respʳ-≈ = RightNaturalOrder.respʳ _≈_  _⊕_ ⊕-isMagma  

  ≤₊-respˡ-≈ : _≤₊_ Respectsˡ _≈_
  ≤₊-respˡ-≈ = RightNaturalOrder.respˡ _≈_  _⊕_ ⊕-isMagma
