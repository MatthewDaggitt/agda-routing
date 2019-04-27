
module RoutingLib.Function.Metric.Rational.Packages where

open import Data.Rational
open import Data.Rational.Properties
open import Function using (const)
open import Level using (Level; 0ℓ; suc) renaming (_⊔_ to _⊔ₗ_)
open import Relation.Binary hiding (Symmetric)
open import Relation.Binary.PropositionalEquality using (_≡_; isEquivalence)

open import RoutingLib.Function.Metric.Rational.Core
open import RoutingLib.Function.Metric.Rational.Structures
open import RoutingLib.Function.Metric.Packages as Base
  using (GeneralMetric)

------------------------------------------------------------------------
-- Many of the simpler packages are simply re-exported

open Base public using
  ( ProtoMetric
  ; PreMetric
  ; QuasiSemiMetric
  ; SemiMetric
  )

------------------------------------------------------------------------
-- Metrics

record Metric a ℓ : Set (suc (a ⊔ₗ ℓ)) where
  field
    Carrier  : Set a
    _≈_      : Rel Carrier ℓ
    d        : Distance Carrier
    isMetric : IsMetric _≈_ d

  open IsMetric isMetric public

  generalMetric : GeneralMetric a 0ℓ ℓ 0ℓ 0ℓ
  generalMetric = record
    { isGeneralMetric = isMetric
    }

  open GeneralMetric generalMetric public
    using (protoMetric; preMetric; quasiSemiMetric; semiMetric)

------------------------------------------------------------------------
-- Ultra-metrics

record UltraMetric a ℓ : Set (suc (a ⊔ₗ ℓ)) where
  field
    Carrier       : Set a
    _≈_           : Rel Carrier ℓ
    d             : Distance Carrier
    isUltraMetric : IsUltraMetric _≈_ d

  open IsUltraMetric isUltraMetric public

  metric : Metric a ℓ
  metric = record
    { isMetric = isMetric
    }

  open Metric metric public
    using (protoMetric; preMetric; quasiSemiMetric; semiMetric; generalMetric)
