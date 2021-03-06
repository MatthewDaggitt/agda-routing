--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module defines the notion of two path-weights being comparable. A pair
-- of path-weights are comparable if there exists a chance that a router may at
-- some point in some computation be forced to choose between them.
--
-- If a pair of nodes are not comparable then we may not need to guarantee that
-- the choice function is well behaved with respect to them (e.g. obeys
-- properties like commutativity). Indeed in some algebras the choice function
-- is only well behaved for comparable path-weights (see
-- `RoutingLib.Routing.Protocols.BGPLite`)
--------------------------------------------------------------------------------

open import Data.Nat using (ℕ) renaming (_≟_ to _≟ℕ_)
open import Function using (_∘_)
open import Level using (_⊔_)
open import Relation.Binary using (Rel; Decidable; Symmetric)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; subst₂)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Basics.Node using (Node)
open import RoutingLib.Routing.Basics.Path.UncertifiedI

module RoutingLib.Routing.Algebra.Comparable
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  where

open RawRoutingAlgebra algebra

private
  variable
    n : ℕ
    i j k : Node n
    w x y z : PathWeight
 
--------------------------------------------------------------------------------
-- Definition
--------------------------------------------------------------------------------
-- This property is defined in a slightly curious way as it appears to include
-- two unnecessary equalities for each constructor. In practice these turn out
-- to be necessary as otherwise it is impossible to pattern match on these
-- constructors when using this definition with an actual routing algebra.

infix 4 _≎_

data _≎_ : Rel PathWeight (a ⊔ b ⊔ ℓ) where
  0∞# : x ≈ 0# → y ≈ ∞# → x ≎ y
  ∞0# : x ≈ ∞# → y ≈ 0# → x ≎ y
  ∞∞# : x ≈ ∞# → y ≈ ∞# → x ≎ y
  0e# : (g : Step i j) (w : PathWeight) → x ≈ 0# → y ≈ g ▷ w → x ≎ y
  e0# : (f : Step i j) (v : PathWeight) → x ≈ f ▷ v → y ≈ 0# → x ≎ y
  ∞e# : (g : Step i j) (w : PathWeight) → x ≈ ∞# → y ≈ g ▷ w → x ≎ y
  e∞# : (f : Step i j) (v : PathWeight) → x ≈ f ▷ v → y ≈ ∞# → x ≎ y
  ee# : (f : Step i j) (g : Step i k) (v w : PathWeight) → j ≢ k → x ≈ f ▷ v → y ≈ g ▷ w → x ≎ y

--------------------------------------------------------------------------------
-- Properties

≎-sym : Symmetric _≎_
≎-sym (0∞# x≈0 y≈∞)               = ∞0# y≈∞ x≈0
≎-sym (∞0# x≈∞ y≈0)               = 0∞# y≈0 x≈∞
≎-sym (∞∞# x≈∞ y≈∞)               = ∞∞# y≈∞ x≈∞
≎-sym (e0# f v x≈fv y≈0)          = 0e# f v y≈0 x≈fv
≎-sym (0e# g w x≈0 y≈gw)          = e0# g w y≈gw x≈0
≎-sym (∞e# f v x≈∞ y≈gw)          = e∞# f v y≈gw x≈∞
≎-sym (e∞# g w x≈fv y≈∞)          = ∞e# g w y≈∞ x≈fv
≎-sym (ee# f g x y j≢k x≈fv y≈gw) = ee# g f y x (j≢k ∘ sym) y≈gw x≈fv

≎-resp-≈ : w ≈ x → y ≈ z → w ≎ y → x ≎ z
≎-resp-≈ w≈x y≈z (0∞# w≈0 y≈∞)               = 0∞# (≈-trans (≈-sym w≈x) w≈0) (≈-trans (≈-sym y≈z) y≈∞)
≎-resp-≈ w≈x y≈z (∞0# w≈∞ y≈0)               = ∞0# (≈-trans (≈-sym w≈x) w≈∞) (≈-trans (≈-sym y≈z) y≈0)
≎-resp-≈ w≈x y≈z (∞∞# w≈∞ y≈∞)               = ∞∞# (≈-trans (≈-sym w≈x) w≈∞) (≈-trans (≈-sym y≈z) y≈∞)
≎-resp-≈ w≈x y≈z (0e# g w w≈0 y≈gw)          = 0e# g w (≈-trans (≈-sym w≈x) w≈0) (≈-trans (≈-sym y≈z) y≈gw)
≎-resp-≈ w≈x y≈z (e0# f v w≈fv y≈0)          = e0# f v (≈-trans (≈-sym w≈x) w≈fv) (≈-trans (≈-sym y≈z) y≈0)
≎-resp-≈ w≈x y≈z (∞e# g w w≈∞ y≈gw)          = ∞e# g w (≈-trans (≈-sym w≈x) w≈∞) (≈-trans (≈-sym y≈z) y≈gw)
≎-resp-≈ w≈x y≈z (e∞# f v w≈fv y≈∞)          = e∞# f v (≈-trans (≈-sym w≈x) w≈fv) (≈-trans (≈-sym y≈z) y≈∞)
≎-resp-≈ w≈x y≈z (ee# f g v w j≢k w≈fv y≈gw) = ee# f g v w j≢k (≈-trans (≈-sym w≈x) w≈fv) (≈-trans (≈-sym y≈z) y≈gw)
