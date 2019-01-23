open import Algebra.FunctionProperties
open import Data.Product
open import Level using (_⊔_)
open import Relation.Binary hiding (Symmetric)
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Construct.NonStrictToStrict as NonStrictToStrict
open import Relation.Nullary using (¬_)
open import Relation.Unary

module RoutingLib.Function.Metric.Core {a i} {A : Set a} {I : Set i} where

{-
open Setoid S renaming (Carrier to A)
open Poset P renaming (Carrier to I; _≈_ to _≈ᵢ_)
open NonStrictToStrict _≈ᵢ_ _≤_ using (_<_)

private
  infix 4 _≉_
  _≉_ : Rel A ℓ₁
  x ≉ y = ¬ (x ≈ y)
-}

------------------------------------------------------------------------
-- Definition

DistanceFunction : Set _
DistanceFunction = A → A → I

Symmetric : ∀ {ℓ} → Rel I ℓ → Pred DistanceFunction (a ⊔ ℓ)
Symmetric _≈_ d = ∀ x y → d x y ≈ d y x

Bounded : ∀ {ℓ} → Rel I ℓ → Pred DistanceFunction (a ⊔ i ⊔ ℓ)
Bounded _≤_ d = ∃ λ n → ∀ x y → d x y ≤ n

TriangleIneq : ∀ {ℓ} → Rel I ℓ → Op₂ I → Pred DistanceFunction (a ⊔ ℓ)
TriangleIneq _≤_ _∙_ d = ∀ x y z → d x z ≤ (d x y ∙ d y z)

------------------------------------------------------------------------
-- Predicates over distance functions

{-
Indiscernable : DistanceFunction → I → Set _
Indiscernable d 0# = ∀ {x y} → d x y ≈ᵢ 0# → x ≈ y

PositiveDefinite : DistanceFunction → I → Set _
PositiveDefinite d 0# = ∀ {x y} → x ≈ y → d x y ≈ᵢ 0#



{-
-}

GeneralTriangleInequality : Op₂ I → Pred DistanceFunction (a₁ ⊔ ℓ₃)
GeneralTriangleInequality _⊕_ d = ∀ x y z → d x z ≤ d x y ⊕ d y z


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
-}
