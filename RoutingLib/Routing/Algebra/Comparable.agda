import Algebra.FunctionProperties as FunctionProperties
open import Data.Nat using (ℕ) renaming (_≟_ to _≟ℕ_)
open import Data.Fin using (Fin)
open import Data.Maybe using (Maybe)
open import Function using (_∘_)
open import Level using (0ℓ; _⊔_)
open import Relation.Binary using (Rel; Decidable; Symmetric)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; subst₂)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Algebra.FunctionProperties using (_Preservesᵇ_)
open import RoutingLib.Data.Maybe.Relation.Cross as Cross
open import RoutingLib.Data.Path.UncertifiedI

open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.Algebra.Comparable
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  where

open RawRoutingAlgebra algebra
open FunctionProperties _≈_

-----------------------------------------------------------------------
-- Comparability

infix 4 _≎_

data _≎_ : Rel Route (a ⊔ b ⊔ ℓ) where
  0∞# : ∀ {x y} → x ≈ 0# → y ≈ ∞  → x ≎ y
  ∞0# : ∀ {x y} → x ≈ ∞  → y ≈ 0# → x ≎ y
  ∞∞# : ∀ {x y} → x ≈ ∞  → y ≈ ∞  → x ≎ y
  0e# : ∀ {x y} → ∀ {n} {i j : Fin n} (g : Step i j) (w : Route) → x ≈ 0# → y ≈ g ▷ w → x ≎ y
  e0# : ∀ {x y} → ∀ {n} {i j : Fin n} (f : Step i j) (v : Route) → x ≈ f ▷ v → y ≈ 0# → x ≎ y
  ∞e# : ∀ {x y} → ∀ {n} {i j : Fin n} (g : Step i j) (w : Route) → x ≈ ∞ → y ≈ g ▷ w → x ≎ y
  e∞# : ∀ {x y} → ∀ {n} {i j : Fin n} (f : Step i j) (v : Route) → x ≈ f ▷ v → y ≈ ∞ → x ≎ y
  ee# : ∀ {x y} → ∀ {n} {i j k : Fin n} (f : Step i j) (g : Step i k) (v w : Route) → j ≢ k → x ≈ f ▷ v → y ≈ g ▷ w → x ≎ y

≎-sym : Symmetric _≎_
≎-sym (0∞# x≈0 y≈∞)               = ∞0# y≈∞ x≈0
≎-sym (∞0# x≈∞ y≈0)               = 0∞# y≈0 x≈∞
≎-sym (∞∞# x≈∞ y≈∞)               = ∞∞# y≈∞ x≈∞
≎-sym (e0# f v x≈fv y≈0)          = 0e# f v y≈0 x≈fv
≎-sym (0e# g w x≈0 y≈gw)          = e0# g w y≈gw x≈0
≎-sym (∞e# f v x≈∞ y≈gw)          = e∞# f v y≈gw x≈∞
≎-sym (e∞# g w x≈fv y≈∞)          = ∞e# g w y≈∞ x≈fv
≎-sym (ee# f g x y j≢k x≈fv y≈gw) = ee# g f y x (j≢k ∘ sym) y≈gw x≈fv

-----------------------------------------------------------------------
-- Some standard algebraic properties lifted to comparability

≎-Associative : Rel Route ℓ → Op₂ Route → Set (a ⊔ b ⊔ ℓ)
≎-Associative _≈_ _⊕_ = ∀ {x y z} → x ≎ y → y ≎ z → x ≎ z →
                        ((x ⊕ y) ⊕ z) ≈ (x ⊕ (y ⊕ z))

ComparablyCommutative : Rel Route ℓ → Op₂ Route → Set (a ⊔ b ⊔ ℓ)
ComparablyCommutative _≈_ _⊕_ = ∀ {x y} → x ≎ y → (x ⊕ y) ≈ (y ⊕ x)

-----------------------------------------------------------------------
-- Properties

module _ (_⊚_ : Op₂ Route) (_≎?_ : Decidable _≎_) where

  _⊗_ : Op₂ Route
  x ⊗ y with x ≎? y
  ... | yes _ = x ⊕ y
  ... | no  _ = x ⊚ y

  fromCompComm : ComparablyCommutative _≈_ _⊕_ → Commutative _⊚_ → Commutative _⊗_
  fromCompComm ccomm comm x y with x ≎? y | y ≎? x
  ... | yes x≎y | yes _   = ccomm x≎y
  ... | yes x≎y | no ¬y≎x = contradiction (≎-sym x≎y) ¬y≎x
  ... | no ¬x≎y | yes y≎x = contradiction (≎-sym y≎x) ¬x≎y
  ... | no  _   | no  _   = comm x y
