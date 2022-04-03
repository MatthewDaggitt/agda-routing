--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module contains the core definitions for routing algebras and some
-- simple associated properties. A routing algebra is an abstract representation
-- of some problem that we want our routing protocol to solve (e.g. the
-- shortest paths problem, the widest paths problem).
--------------------------------------------------------------------------------

open import Algebra
open import Data.Fin using (toℕ)
open import Data.List using (List)
import Data.List.Membership.Setoid as ListMembership
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; ∃₂; _,_)
open import Data.Sum using (_⊎_)
open import Level using (Lift; lift; _⊔_) renaming (suc to lsuc)
open import Function using (_∘_)
open import Relation.Nullary using (¬_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_)

open import RoutingLib.Relation.Nullary.Finite.List.Setoid using (Finite)

import RoutingLib.Routing.Basics.Path.UncertifiedI as UncertifiedPaths
import RoutingLib.Routing.Basics.Path.CertifiedI as CertifiedPaths
open import RoutingLib.Routing.Basics.Node

module RoutingLib.Routing.Algebra where

--------------------------------------------------------------------------------
-- Raw routing algebras --
--------------------------------------------------------------------------------
-- This definition defines the structure of a routing algebra. In this record
-- the algebra is not assumed to have any of the natural properties we would
-- expect, only that the operations respect the associated notion of equality
-- over path-weights.
--
-- These raw structures are useful when one algebra that may
-- not technically be a routing algebra but still simulates a true routing
-- algebra. 

open import RoutingLib.Routing.Algebra.Core public

--------------------------------------------------------------------------------
-- Basic properties
--------------------------------------------------------------------------------
-- Basic important properties an algebra may possess

module _ {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) where

  open RawRoutingAlgebra algebra
  open ListMembership S renaming (_∈_ to _∈ₗ_)

  -- Distributivity = you and your neighbour's choices always agree
  IsDistributive : Set _
  IsDistributive = ∀ {n} {i j : Node n} (f : Step i j) x y → f ▷ (x ⊕ y) ≈ (f ▷ x) ⊕ (f ▷ y)
  
  -- Increasing = extending a path-weight never makes it better
  IsIncreasing : Set _
  IsIncreasing = ∀ {n} {i j : Node n} (f : Step i j) x → x ≤₊ (f ▷ x)

  -- Strictly increasing = extending a path-weight always makes it worse
  IsStrictlyIncreasing : Set _
  IsStrictlyIncreasing = ∀ {n} {i j : Node n} (f : Step i j) {x} → x ≉ ∞# → x <₊ (f ▷ x)

  -- Finite = there only exist a finite number of path-weights
  IsFinite : Set _
  IsFinite = Finite S

  Level_DistributiveIn[_,_] : ℕ → PathWeight → PathWeight → Set _
  Level 0       DistributiveIn[ ⊥ , ⊤ ] =
    ∀ {n} {i j : Node n} (f : Step i j) →
    ∀ {x y} → ⊥ ≤₊ x → x ≤₊ ⊤ → ⊥ ≤₊ y → y ≤₊ ⊤ →
    f ▷ (x ⊕ y) ≈ (f ▷ x) ⊕ (f ▷ y) 
  Level (suc k) DistributiveIn[ ⊥ , ⊤ ] =
    ∀ {n} {i j : Node n} (f : Step i j) →
    ∀ {x y} → ⊥ ≤₊ x → x ≤₊ ⊤ → ⊥ ≤₊ y → y ≤₊ ⊤ →
    Level k DistributiveIn[ f ▷ (x ⊕ y) , (f ▷ x) ⊕ (f ▷ y) ]

  IsLevel_Distributive : ℕ → Set _
  IsLevel k Distributive = Level k DistributiveIn[ 0# , ∞# ]

  Level_DistributiveIn[_,_]Alt : ℕ → PathWeight → PathWeight → Set _
  Level 0       DistributiveIn[ ⊥ , ⊤ ]Alt = Lift (a ⊔ b ⊔ ℓ) (⊥ ≈ ⊤)
  Level (suc k) DistributiveIn[ ⊥ , ⊤ ]Alt =
    ∀ {n} {i j : Node n} (f : Step i j) →
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
      ▷-fixedPoint : ∀ {n} {i j : Node n} (f : Step i j) → f ▷ ∞# ≈ ∞#

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
      path           : PathWeight → Path
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
      path-reject    : ∀ {n} {i j : Node n} {r p} (f : Step i j) → path r ≡ valid p →
                       (¬ (toℕ i , toℕ j) ⇿ᵥ p) ⊎ toℕ i ∈ᵥₚ p → f ▷ r ≈ ∞#
      -- The extension of a route along a valid edge always actually adds that
      -- edge to the path.
      path-accept    : ∀ {n} {i j : Node n} {r p} (f : Step i j) → path r ≡ valid p →
                       f ▷ r ≉ ∞# → path (f ▷ r) ≡ valid ((toℕ i , toℕ j) ∷ p)

--------------------------------------------------------------------------------
-- Certified path algebras
--------------------------------------------------------------------------------
-- This is an alternative more convenient internal representation of a path
-- algebra used by the various proofs in the library. The difference is that
-- in a certified path algebra the path-weights themselves contain proofs that they
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
      path           : PathWeight → Path n
      path-cong      : path Preserves _≈_ ⟶ _≈ₚ_
      r≈0⇒path[r]≈[] : ∀ {r} → r ≈ 0# → path r ≈ₚ trivial
      r≈∞⇒path[r]≈∅  : ∀ {r} → r ≈ ∞# → path r ≈ₚ invalid
      path[r]≈∅⇒r≈∞  : ∀ {r} → path r ≈ₚ invalid → r ≈ ∞#
      path-reject    : ∀ {i j : Node n} {r p} (f : Step i j) → path r ≈ₚ valid p →
                       (¬ (i , j) ⇿ᵛ p) ⊎ i ∈ᵥₚ p → f ▷ r ≈ ∞#
      path-accept    : ∀ {i j : Node n} {r p} (f : Step i j) → path r ≈ₚ valid p → f ▷ r ≉ ∞# →
                       ∀ ij⇿p i∉p → path (f ▷ r) ≈ₚ valid ((i , j) ∷ p ∣ ij⇿p ∣ i∉p)

    -- Functions

    size : PathWeight → ℕ
    size r = length (path r)

    weight : (∀ i j → Step i j) → Path n → PathWeight
    weight A invalid                       = ∞#
    weight A trivial                       = 0#
    weight A (valid ((i , j) ∷ p ∣ _ ∣ _)) = A i j ▷ weight A (valid p)


module PathDistributivity
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isPathAlgebra : IsPathAlgebra algebra)
  where

  open RawRoutingAlgebra algebra
  open IsPathAlgebra isPathAlgebra
  open UncertifiedPaths

  PathDistributive : Set _
  PathDistributive = ∀ {n} {i j : Node n} (f : Step i j) →
                     ∀ {x y} → toℕ i ∉ₚ path x → toℕ i ∉ₚ path y → f ▷ (x ⊕ y) ≈ (f ▷ x) ⊕ (f ▷ y)


  IsLevel_PathDistributiveIn[_,_]Alt : ℕ → PathWeight → PathWeight → Set _
  IsLevel 0       PathDistributiveIn[ ⊥ , ⊤ ]Alt = Lift (a ⊔ b ⊔ ℓ) (⊥ ≈ ⊤)
  IsLevel (suc k) PathDistributiveIn[ ⊥ , ⊤ ]Alt =
    ∀ {n} {i j : Node n} (f : Step i j) →
    ∀ {x y} → ⊥ ≤₊ x → x ≤₊ ⊤ → ⊥ ≤₊ y → y ≤₊ ⊤ →
    toℕ i ∉ₚ path x → toℕ i ∉ₚ path y →
    (toℕ i , toℕ j) ⇿ path x → (toℕ i , toℕ j) ⇿ path y →
    IsLevel k PathDistributiveIn[ f ▷ (x ⊕ y) , (f ▷ x) ⊕ (f ▷ y) ]Alt


  -- kᵗʰ level distributivity
  IsLevel_PathDistributiveIn[_,_] : ℕ → PathWeight → PathWeight → Set _
  IsLevel 0       PathDistributiveIn[ ⊥ , ⊤ ] =
    ∀ {n} {i j : Node n} (f : Step i j) →
    ∀ {x y} → ⊥ ≤₊ x → x ≤₊ ⊤ → ⊥ ≤₊ y → y ≤₊ ⊤ →
    toℕ i ∉ₚ path x → toℕ i ∉ₚ path y →
    (toℕ i , toℕ j) ⇿ path x → (toℕ i , toℕ j) ⇿ path y →
    f ▷ (x ⊕ y) ≈ (f ▷ x) ⊕ (f ▷ y) 
  IsLevel (suc k) PathDistributiveIn[ ⊥ , ⊤ ] =
    ∀ {n} {i j : Node n} (f : Step i j) →
    ∀ {x y} → ⊥ ≤₊ x → x ≤₊ ⊤ → ⊥ ≤₊ y → y ≤₊ ⊤ →
    toℕ i ∉ₚ path x → toℕ i ∉ₚ path y →
    IsLevel k PathDistributiveIn[ f ▷ (x ⊕ y) , (f ▷ x) ⊕ (f ▷ y) ]
  
  IsLevel_PathDistributive : ℕ → Set _
  IsLevel k PathDistributive = IsLevel k PathDistributiveIn[ 0# , ∞# ]
