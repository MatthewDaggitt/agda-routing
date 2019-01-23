open import Data.Nat hiding (suc)
open import Data.Nat.Properties
open import Function using (const)
open import Level using (0ℓ; suc) renaming (_⊔_ to _⊔ₗ_)
open import Relation.Binary hiding (Symmetric)
open import Relation.Binary.PropositionalEquality using (_≡_; isEquivalence)

open import RoutingLib.Function.Metric as BasePackages using (GeneralMetric)
open import RoutingLib.Function.Metric.Structures as BaseStructures using (IsGeneralMetric)
import RoutingLib.Function.Metric.Core as BaseCore

module RoutingLib.Function.Metric.Nat where

module _ {a} {A : Set a} where

  Symmetric : (A → A → ℕ) → Set a
  Symmetric = BaseCore.Symmetric _≡_

  Bounded : (A → A → ℕ) → Set a
  Bounded = BaseCore.Bounded _≤_

  MaxTriangleInequality : (A → A → ℕ) → Set a
  MaxTriangleInequality = BaseCore.TriangleIneq _≤_ _⊔_

------------------------------------------------------------------------
-- Packages

module _ {a ℓ} {A : Set a} where

  IsPreMetric : Rel A ℓ → (A → A → ℕ) → Set (a ⊔ₗ ℓ)
  IsPreMetric _≈_ = BaseStructures.IsPreMetric _≈_ _≡_ _≤_ 0

  open BaseStructures using (module IsPreMetric) public

  IsQuasiSemiMetric : Rel A ℓ → (A → A → ℕ) → Set (a ⊔ₗ ℓ)
  IsQuasiSemiMetric _≈_ = BaseStructures.IsQuasiSemiMetric _≈_ _≡_ _≤_ 0

  open BaseStructures using (module IsQuasiSemiMetric) public

  IsSemiMetric : Rel A ℓ → (A → A → ℕ) → Set (a ⊔ₗ ℓ)
  IsSemiMetric _≈_ = BaseStructures.IsSemiMetric _≈_ _≡_ _≤_ 0

  open BaseStructures using (module IsSemiMetric) public

  IsMetric : Rel A ℓ → (A → A → ℕ) → Set (a ⊔ₗ ℓ)
  IsMetric _≈_ = BaseStructures.IsGeneralMetric _≈_ _≡_ _≤_ 0 _+_

  module IsMetric {_≈_ d} (M : IsMetric _≈_ d) where
    open BaseStructures.IsGeneralMetric M public

  IsUltraMetric : Rel A ℓ → (A → A → ℕ) → Set (a ⊔ₗ ℓ)
  IsUltraMetric _≈_ = BaseStructures.IsGeneralMetric _≈_ _≡_ _≤_ 0 _⊔_

  module IsUltraMetric {_≈_ d} (UM : IsUltraMetric _≈_ d) where
    open BaseStructures.IsGeneralMetric UM public

------------------------------------------------------------------------
-- Packages

open BasePackages public using
  ( PreMetric
  ; QuasiSemiMetric
  ; SemiMetric
  )

record Metric a ℓ : Set (suc (a ⊔ₗ ℓ)) where
  field
    Carrier  : Set a
    _≈_      : Rel Carrier ℓ
    d        : Carrier → Carrier → ℕ
    isMetric : IsMetric _≈_ d

  open IsGeneralMetric isMetric public

  generalMetric : GeneralMetric a 0ℓ ℓ 0ℓ 0ℓ
  generalMetric = record { isGeneralMetric = isMetric }


record UltraMetric a ℓ : Set (suc (a ⊔ₗ ℓ)) where
  field
    Carrier       : Set a
    _≈_           : Rel Carrier ℓ
    d             : Carrier → Carrier → ℕ
    isUltraMetric : IsUltraMetric _≈_ d

  open IsGeneralMetric isUltraMetric

  isMetric : IsMetric _≈_ d
  isMetric = record
    { isSemiMetric = isSemiMetric
    ; triangle     = λ x y z → ≤-trans (triangle x y z) (m⊔n≤m+n (d x y) (d y z))
    }

  metric : Metric a ℓ
  metric = record { isMetric = isMetric }
