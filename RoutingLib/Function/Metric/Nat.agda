open import Data.Nat hiding (suc)
open import Data.Nat.Properties
open import Function using (const)
open import Level using (0ℓ; suc) renaming (_⊔_ to _⊔ₗ_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; isEquivalence)

open import RoutingLib.Function.Metric as BasePackages using (GeneralMetric)
open import RoutingLib.Function.Metric.Structures as BaseStructures using (IsGeneralMetric)

module RoutingLib.Function.Metric.Nat where

------------------------------------------------------------------------
-- Packages

module _ {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) where

  IsPreMetric : (A → A → ℕ) → Set (a ⊔ₗ ℓ)
  IsPreMetric = BaseStructures.IsPreMetric _≈_ _≡_ _≤_ 0

  IsQuasiSemiMetric : (A → A → ℕ) → Set (a ⊔ₗ ℓ)
  IsQuasiSemiMetric = BaseStructures.IsQuasiSemiMetric _≈_ _≡_ _≤_ 0

  IsSemiMetric : (A → A → ℕ) → Set (a ⊔ₗ ℓ)
  IsSemiMetric = BaseStructures.IsSemiMetric _≈_ _≡_ _≤_ 0

  IsMetric : (A → A → ℕ) → Set (a ⊔ₗ ℓ)
  IsMetric = BaseStructures.IsGeneralMetric _≈_ _≡_ _≤_ 0 _+_

  IsUltraMetric : (A → A → ℕ) → Set (a ⊔ₗ ℓ)
  IsUltraMetric = BaseStructures.IsGeneralMetric _≈_ _≡_ _≤_ 0 _⊔_

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
