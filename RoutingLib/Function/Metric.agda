open import Algebra.FunctionProperties using (Op₁; Op₂)
open import Data.Nat.Properties using (≤⇒≤′)
open import Level using (suc; _⊔_)
open import Relation.Binary hiding (Symmetric)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (sym to ≡-sym)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred)
open import Data.Product using (∃; _,_)
open import Induction.WellFounded using (Acc; acc)

open import RoutingLib.Function.Metric.Structures

module RoutingLib.Function.Metric where

------------------------------------------------------------------------
-- PreMetric

open import RoutingLib.Function.Metric.Core public

------------------------------------------------------------------------
-- PreMetric

record PreMetric a i ℓ₁ ℓ₂ ℓ₃ : Set (suc (a ⊔ i ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
  field
    Carrier     : Set a
    Image       : Set i
    _≈_         : Rel Carrier ℓ₁
    _≈ᵢ_        : Rel Image ℓ₂
    _≤_         : Rel Image ℓ₃
    0#          : Image
    d           : Carrier → Carrier → Image
    isPreMetric : IsPreMetric _≈_ _≈ᵢ_ _≤_ 0# d

  open IsPreMetric isPreMetric public

------------------------------------------------------------------------
-- QuasiSemiMetric

record QuasiSemiMetric a i ℓ₁ ℓ₂ ℓ₃ : Set (suc (a ⊔ i ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
  field
    Carrier           : Set a
    Image             : Set i
    _≈_               : Rel Carrier ℓ₁
    _≈ᵢ_              : Rel Image ℓ₂
    _≤_               : Rel Image ℓ₃
    0#                : Image
    d                 : Carrier → Carrier → Image
    isQuasiSemiMetric : IsQuasiSemiMetric _≈_ _≈ᵢ_ _≤_ 0# d

  open IsQuasiSemiMetric isQuasiSemiMetric public

------------------------------------------------------------------------
-- SemiMetric

record SemiMetric a i ℓ₁ ℓ₂ ℓ₃ : Set (suc (a ⊔ i ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
  field
    Carrier      : Set a
    Image        : Set i
    _≈_          : Rel Carrier ℓ₁
    _≈ᵢ_         : Rel Image ℓ₂
    _≤_          : Rel Image ℓ₃
    0#           : Image
    d            : Carrier → Carrier → Image
    isSemiMetric : IsSemiMetric _≈_ _≈ᵢ_ _≤_ 0# d

  open IsSemiMetric isSemiMetric public

------------------------------------------------------------------------
-- GeneralMetric

-- Note that this package is not necessarily a metric in the classical
-- sense as there is no way to ensure that the _∙_ operator really
-- represents addition. See `Function.Metric.Nat` and
-- `Function.Metric.Rational` for more specialised `Metric` and
-- `UltraMetric` packages.

record GeneralMetric a i ℓ₁ ℓ₂ ℓ₃ : Set (suc (a ⊔ i ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
  field
    Carrier         : Set a
    Image           : Set i
    _≈_             : Rel Carrier ℓ₁
    _≈ᵢ_            : Rel Image ℓ₂
    _≤_             : Rel Image ℓ₃
    0#              : Image
    _∙_             : Op₂ Image
    d               : Carrier → Carrier → Image
    isGeneralMetric : IsGeneralMetric _≈_ _≈ᵢ_ _≤_ 0# _∙_ d

  open IsGeneralMetric isGeneralMetric public
