open import Relation.Binary hiding (Symmetric)

module RoutingLib.Function.Metric.Structures
  {a i ℓ₁ ℓ₂ ℓ₃} {A : Set a} {I : Set i}
  (_≈ₐ_ : Rel A ℓ₁) (_≈ᵢ_ : Rel I ℓ₂) (_≤_ : Rel I ℓ₃) (0# : I) where

open import Algebra.Core using (Op₁; Op₂)
open import Data.Nat.Properties using (≤⇒≤′)
open import Data.Product using (∃; _,_)
open import RoutingLib.Function.Metric.Core
open import Level using (suc; _⊔_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred)

------------------------------------------------------------------------
-- Proto-metrics

record IsProtoMetric (d : Distance A I) : Set (a ⊔ i ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  field
    isPartialOrder   : IsPartialOrder _≈ᵢ_ _≤_
    ≈-isEquivalence  : IsEquivalence _≈ₐ_
    cong             : d Preserves₂ _≈ₐ_ ⟶ _≈ₐ_ ⟶ _≈ᵢ_
    0#-minimum       : ∀ {x y} → 0# ≤ d x y

  open IsPartialOrder isPartialOrder public
    renaming (module Eq to ImageEq)

  module CarrierEq = IsEquivalence ≈-isEquivalence

------------------------------------------------------------------------
-- Pre-metrics

record IsPreMetric (d : Distance A I) : Set (a ⊔ i ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  field
    isProtoMetric : IsProtoMetric d
    eq⇒0          : Definite _≈ₐ_ _≈ᵢ_ d 0#

  open IsProtoMetric isProtoMetric public

------------------------------------------------------------------------
-- Quasi-semi-metrics

record IsQuasiSemiMetric (d : Distance A I) : Set (a ⊔ i ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  field
    isPreMetric      : IsPreMetric d
    0⇒eq             : ∀ {x y} → d x y ≈ᵢ 0# → x ≈ₐ y

  open IsPreMetric isPreMetric public

------------------------------------------------------------------------
-- Semi-metrics

record IsSemiMetric (d : Distance A I) : Set (a ⊔ i ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  field
    isQuasiSemiMetric : IsQuasiSemiMetric d
    sym               : Symmetric _≈ᵢ_ d

  open IsQuasiSemiMetric isQuasiSemiMetric public

------------------------------------------------------------------------
-- General metrics

-- A general metric obeys a generalised form of the triangle inequality.
-- It can be specialised to a standard metric/ultrametric/inframetric etc.
-- by providing the correct operator.

record IsGeneralMetric (_∙_ : Op₂ I) (d : Distance A I) : Set (a ⊔ i ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  field
    isSemiMetric : IsSemiMetric d
    triangle     : TriangleIneq _≤_ _∙_ d

  open IsSemiMetric isSemiMetric public
