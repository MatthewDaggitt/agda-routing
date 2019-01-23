open import Algebra.FunctionProperties using (Op₁; Op₂)
open import Data.Nat.Properties using (≤⇒≤′)
open import Level using (suc; _⊔_)
open import Relation.Binary hiding (Symmetric)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred)
open import Data.Product using (∃; _,_)
open import Induction.WellFounded using (Acc; acc)

module RoutingLib.Function.Metric.Structures
  {a i ℓ₁ ℓ₂ ℓ₃} {A : Set a} {I : Set i}
  (_≈_ : Rel A ℓ₁) (_≈ᵢ_ : Rel I ℓ₂) (_≤_ : Rel I ℓ₃) (0# : I) where

------------------------------------------------------------------------
-- Types of metric structures

record IsPreMetric (d : A → A → I) : Set (a ⊔ i ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  field
    isTotalOrder     : IsTotalOrder _≈ᵢ_ _≤_
    ≈-isEquivalence  : IsEquivalence _≈_
    cong             : d Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈ᵢ_
    eq⇒0             : ∀ {x y} → x ≈ y → d x y ≈ᵢ 0#
    0#-minimum       : ∀ {x y} → 0# ≤ d x y

  open IsTotalOrder isTotalOrder public

record IsQuasiSemiMetric (d : A → A → I) : Set (a ⊔ i ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  field
    isPreMetric      : IsPreMetric d
    0⇒eq             : ∀ {x y} → d x y ≈ᵢ 0# → x ≈ y

  open IsPreMetric isPreMetric public

record IsSemiMetric (d : A → A → I) : Set (a ⊔ i ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  field
    isQuasiSemiMetric : IsQuasiSemiMetric d
    sym               : ∀ x y → d x y ≈ᵢ d y x

  open IsQuasiSemiMetric isQuasiSemiMetric public

-- A general metric obeys a generalised form of the triangle inequality.
-- It can be specialised to a standard metric/ultrametric/inframetric etc. by
-- providing the correct operator.

record IsGeneralMetric (_∙_ : Op₂ I) (d : A → A → I) : Set (a ⊔ i ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where

  field
    isSemiMetric : IsSemiMetric d
    triangle     : ∀ x y z → d x z ≤ (d x y ∙ d y z)

  open IsSemiMetric isSemiMetric public
