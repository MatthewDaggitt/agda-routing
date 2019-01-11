open import Algebra.FunctionProperties
open import Data.Product
open import Level using (_⊔_)
open import Relation.Binary hiding (Symmetric)
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Construct.NonStrictToStrict as NonStrictToStrict
open import Relation.Nullary using (¬_)
open import Relation.Unary

module RoutingLib.Function.Metric.Core {a₁ a₂ ℓ₁ ℓ₂ ℓ₃}
  (S : Setoid a₁ ℓ₁) (P : Poset a₂ ℓ₂ ℓ₃)
  where

open Setoid S renaming (Carrier to A)
open Poset P renaming (Carrier to I; _≈_ to _≈ᵢ_)
open NonStrictToStrict _≈ᵢ_ _≤_ using (_<_)

private
  infix 4 _≉_
  _≉_ : Rel A ℓ₁
  x ≉ y = ¬ (x ≈ y)

------------------------------------------------------------------------
-- Definition

DistanceFunction : Set _
DistanceFunction = A → A → I

------------------------------------------------------------------------
-- Predicates over distance functions

Indiscernable : DistanceFunction → I → Set _
Indiscernable d 0# = ∀ {x y} → d x y ≈ᵢ 0# → x ≈ y

PositiveDefinite : DistanceFunction → I → Set _
PositiveDefinite d 0# = ∀ {x y} → x ≈ y → d x y ≈ᵢ 0#

Symmetric : Pred DistanceFunction (a₁ ⊔ ℓ₂)
Symmetric d = ∀ x y → d x y ≈ᵢ d y x

{-
TriangleIneq : Pred DistanceFunction a₁
TriangleIneq d = ∀ x y z → d x z ≤ d x y + d y z
-}

GeneralTriangleInequality : Op₂ I → Pred DistanceFunction (a₁ ⊔ ℓ₃)
GeneralTriangleInequality _⊕_ d = ∀ x y z → d x z ≤ d x y ⊕ d y z

Bounded : Pred DistanceFunction (a₁ ⊔ a₂ ⊔ ℓ₃)
Bounded d = ∃ λ n → ∀ x y → d x y ≤ n

_ContrOver_ : Op₁ A → DistanceFunction → Set _
f ContrOver d = ∀ x y → d (f x) (f y) ≤ d x y

_StrContrOver_ : Op₁ A → DistanceFunction → Set _
f StrContrOver d = ∀ {x y} → y ≉ x → d (f x) (f y) < d x y

_ContrOnOrbitsOver_ : Op₁ A → DistanceFunction → Set _
f ContrOnOrbitsOver d = ∀ x → d (f x) (f (f x)) ≤ d x (f x)

_StrContrOnOrbitsOver_ : Op₁ A → DistanceFunction → Set _
f StrContrOnOrbitsOver d = ∀ {x} → f x ≉ x → d (f x) (f (f x)) < d x (f x)

_StrContrOnFixedPointOver_ : Op₁ A → DistanceFunction → Set _
f StrContrOnFixedPointOver d = ∀ {x x*} → f x* ≈ x* → x ≉ x* → d x* (f x) < d x* x
