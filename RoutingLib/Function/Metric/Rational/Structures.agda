
module RoutingLib.Function.Metric.Rational.Structures where

open import Data.Rational
open import Data.Rational.Properties
open import Level using (Level; 0ℓ; suc) renaming (_⊔_ to _⊔ₗ_)
open import Relation.Binary hiding (Symmetric)
open import Relation.Binary.PropositionalEquality using (_≡_; isEquivalence)

open import RoutingLib.Data.Rational
open import RoutingLib.Data.Rational.Properties
open import RoutingLib.Function.Metric.Rational.Core
import RoutingLib.Function.Metric.Structures as Base

private
  variable
    a ℓ : Level
    A   : Set a
    _≈_ : Rel A ℓ
    d   : A → A → ℚ

------------------------------------------------------------------------
-- Proto-metrics

IsProtoMetric : Rel A ℓ → Distance A → Set _
IsProtoMetric _≈_ = Base.IsProtoMetric _≈_ _≡_ _≤_ 0ℚ

open Base using (module IsProtoMetric) public

------------------------------------------------------------------------
-- Pre-metrics

IsPreMetric : Rel A ℓ → Distance A → Set _
IsPreMetric _≈_ = Base.IsPreMetric _≈_ _≡_ _≤_ 0ℚ

open Base using (module IsPreMetric) public

------------------------------------------------------------------------
-- Quasi-semi-metrics

IsQuasiSemiMetric : Rel A ℓ → Distance A → Set _
IsQuasiSemiMetric _≈_ = Base.IsQuasiSemiMetric _≈_ _≡_ _≤_ 0ℚ

open Base using (module IsQuasiSemiMetric) public

------------------------------------------------------------------------
-- Semi-metrics

IsSemiMetric : Rel A ℓ → Distance A → Set _
IsSemiMetric _≈_ = Base.IsSemiMetric _≈_ _≡_ _≤_ 0ℚ

open Base using (module IsSemiMetric) public

------------------------------------------------------------------------
-- Metrics

IsMetric : Rel A ℓ → Distance A → Set _
IsMetric _≈_ = Base.IsGeneralMetric _≈_ _≡_ _≤_ 0ℚ _+_

module IsMetric (M : IsMetric _≈_ d) where
  open Base.IsGeneralMetric M public

------------------------------------------------------------------------
-- Ultra-metrics

IsUltraMetric : Rel A ℓ → Distance A → Set _
IsUltraMetric _≈_ = Base.IsGeneralMetric _≈_ _≡_ _≤_ 0ℚ _⊔_

module IsUltraMetric (UM : IsUltraMetric _≈_ d) where
  open Base.IsGeneralMetric UM public

  isMetric : IsMetric _≈_ d
  isMetric = record
    { isSemiMetric = isSemiMetric
    ; triangle     = λ x y z → ≤-trans (triangle x y z) (p⊔q≤p+q (d x y) (d y z))
    }
