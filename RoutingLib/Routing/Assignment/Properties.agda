--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module contains the basic definitions about the assignment of a route
-- to a node.
--------------------------------------------------------------------------------

open import Data.Fin.Base as Fin using (Fin)
open import Data.Fin.Properties as Fin using (any?)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; ∃₂; proj₁; proj₂)
import Data.Product.Relation.Binary.Pointwise.NonDependent as DirectProduct
import Data.Product.Relation.Binary.Lex.NonStrict as LexProduct
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (¬?; ¬-reflects)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary as U using (Pred; _∈_; ∁)
import Relation.Binary.Construct.NonStrictToStrict as NonStrictToStrict

import RoutingLib.Relation.Binary.PropositionalEquality as ≡

open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.Assignment.Properties
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (n : ℕ)
  where

open RawRoutingAlgebra algebra
open IsRoutingAlgebra isRoutingAlgebra

open import RoutingLib.Routing.Assignment algebra n
open import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra isRoutingAlgebra

--------------------------------------------------------------------------------
-- Properties of _≤ₐₚ_

≤ₐₚ-poset : Poset a ℓ ℓ
≤ₐₚ-poset = DirectProduct.×-poset (≡.poset (Fin n)) ≤₊-poset

--------------------------------------------------------------------------------
-- Properties of _≤ₐₜ_

≤ₐₜ-decTotalOrder : DecTotalOrder a ℓ ℓ
≤ₐₜ-decTotalOrder = LexProduct.×-decTotalOrder (Fin.≤-decTotalOrder n) ≤₊-decTotalOrder

open DecTotalOrder ≤ₐₜ-decTotalOrder public
  using () renaming
  ( ≤-respˡ-≈       to ≤ₐₜ-respˡ-≈ₐ
  ; ≤-respʳ-≈       to ≤ₐₜ-respʳ-≈ₐ
  ; refl            to ≤ₐₜ-refl
  ; reflexive       to ≤ₐₜ-reflexive
  ; trans           to ≤ₐₜ-trans
  ; antisym         to ≤ₐₜ-antisym
  ; total           to ≤ₐₜ-total
  ; isPreorder      to ≤ₐₜ-isPreorder
  ; totalOrder      to ≤ₐₜ-totalOrder
  ; isDecTotalOrder to ≤ₐₜ-isDecTotalOrder
  )
    
--------------------------------------------------------------------------------
-- Properties of _<ₐₜ_

<ₐₜ-isStrictTotalOrder : IsStrictTotalOrder _≈ₐ_ _<ₐₜ_
<ₐₜ-isStrictTotalOrder = NonStrictToStrict.<-isStrictTotalOrder₂ _≈ₐ_ _≤ₐₜ_ ≤ₐₜ-isDecTotalOrder

<ₐₜ-strictTotalOrder : StrictTotalOrder a ℓ ℓ
<ₐₜ-strictTotalOrder = record
  { isStrictTotalOrder = <ₐₜ-isStrictTotalOrder
  }

open StrictTotalOrder <ₐₜ-strictTotalOrder public
  using ()
  renaming
  ( <-resp-≈  to <ₐₜ-resp-≈ₐ
  ; irrefl    to <ₐₜ-irrefl
  ; compare   to <ₐₜ-cmp
  ; asym      to <ₐₜ-asym
  )

<ₐₜ-≤ₐₜ-trans : Trans _<ₐₜ_ _≤ₐₜ_ _<ₐₜ_
<ₐₜ-≤ₐₜ-trans = NonStrictToStrict.<-≤-trans _ _≤ₐₜ_ ≈ₐ-sym ≤ₐₜ-trans ≤ₐₜ-antisym ≤ₐₜ-respʳ-≈ₐ

≮ₐₜ∧≯ₐₜ⇒≈ₐ : ∀ {x y} → ¬ (x <ₐₜ y) → ¬ (y <ₐₜ x) → x ≈ₐ y
≮ₐₜ∧≯ₐₜ⇒≈ₐ {x} {y} ¬x<y ¬y<x with <ₐₜ-cmp x y
... | tri< x<y _   _   = contradiction x<y ¬x<y
... | tri≈ _   x≈y _   = x≈y
... | tri> _   _   y<x = contradiction y<x ¬y<x
