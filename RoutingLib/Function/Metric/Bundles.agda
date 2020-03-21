
open import Level using (Level; suc; _⊔_)

module RoutingLib.Function.Metric.Bundles (a i ℓ₁ ℓ₂ ℓ₃ : Level) where

open import Algebra.Core using (Op₂)
open import Data.Nat.Properties using (≤⇒≤′)
open import Relation.Binary hiding (Symmetric)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (sym to ≡-sym)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred)
open import Data.Product using (∃; _,_)
open import Induction.WellFounded using (Acc; acc)

open import RoutingLib.Function.Metric.Structures
open import RoutingLib.Function.Metric.Core

private
  ℓ = suc (a ⊔ i ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)

------------------------------------------------------------------------
-- ProtoMetric

record ProtoMetric : Set ℓ where
  field
    Carrier       : Set a
    Image         : Set i
    _≈_           : Rel Carrier ℓ₁
    _≈ᵢ_          : Rel Image ℓ₂
    _≤_           : Rel Image ℓ₃
    0#            : Image
    d             : Distance Carrier Image
    isProtoMetric : IsProtoMetric _≈_ _≈ᵢ_ _≤_ 0# d

  open IsProtoMetric isProtoMetric public

------------------------------------------------------------------------
-- PreMetric

record PreMetric : Set ℓ where
  field
    Carrier     : Set a
    Image       : Set i
    _≈_         : Rel Carrier ℓ₁
    _≈ᵢ_        : Rel Image ℓ₂
    _≤_         : Rel Image ℓ₃
    0#          : Image
    d           : Distance Carrier Image
    isPreMetric : IsPreMetric _≈_ _≈ᵢ_ _≤_ 0# d

  open IsPreMetric isPreMetric public

  protoMetric : ProtoMetric
  protoMetric = record { isProtoMetric = isProtoMetric }

------------------------------------------------------------------------
-- QuasiSemiMetric

record QuasiSemiMetric : Set ℓ where
  field
    Carrier           : Set a
    Image             : Set i
    _≈_               : Rel Carrier ℓ₁
    _≈ᵢ_              : Rel Image ℓ₂
    _≤_               : Rel Image ℓ₃
    0#                : Image
    d                 : Distance Carrier Image
    isQuasiSemiMetric : IsQuasiSemiMetric _≈_ _≈ᵢ_ _≤_ 0# d

  open IsQuasiSemiMetric isQuasiSemiMetric public

  preMetric : PreMetric
  preMetric = record { isPreMetric = isPreMetric }

  open PreMetric preMetric public
    using (protoMetric)

------------------------------------------------------------------------
-- SemiMetric

record SemiMetric : Set ℓ where
  field
    Carrier      : Set a
    Image        : Set i
    _≈_          : Rel Carrier ℓ₁
    _≈ᵢ_         : Rel Image ℓ₂
    _≤_          : Rel Image ℓ₃
    0#           : Image
    d            : Distance Carrier Image
    isSemiMetric : IsSemiMetric _≈_ _≈ᵢ_ _≤_ 0# d

  open IsSemiMetric isSemiMetric public

  quasiSemiMetric : QuasiSemiMetric
  quasiSemiMetric = record { isQuasiSemiMetric = isQuasiSemiMetric }

  open QuasiSemiMetric quasiSemiMetric public
    using (protoMetric; preMetric)

------------------------------------------------------------------------
-- GeneralMetric

-- Note that this package is not necessarily a metric in the classical
-- sense as there is no way to ensure that the _∙_ operator really
-- represents addition. See `Function.Metric.Nat` and
-- `Function.Metric.Rational` for more specialised `Metric` and
-- `UltraMetric` packages.

record GeneralMetric : Set ℓ where
  field
    Carrier         : Set a
    Image           : Set i
    _≈_             : Rel Carrier ℓ₁
    _≈ᵢ_            : Rel Image ℓ₂
    _≤_             : Rel Image ℓ₃
    0#              : Image
    _∙_             : Op₂ Image
    d               : Distance Carrier Image
    isGeneralMetric : IsGeneralMetric _≈_ _≈ᵢ_ _≤_ 0# _∙_ d

  open IsGeneralMetric isGeneralMetric public

  semiMetric : SemiMetric
  semiMetric = record { isSemiMetric = isSemiMetric }

  open SemiMetric semiMetric public
    using (protoMetric; preMetric; quasiSemiMetric)
