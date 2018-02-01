open import Level using () renaming (_⊔_ to _⊔ₗ_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_; _⊔_; _<′_)
open import Data.Nat.Properties using (≤⇒≤′)
open import Relation.Binary using (Setoid; Decidable; _Preserves_⟶_; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (sym to ≡-sym)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred)
open import Data.Product using (∃; _,_)
open import Induction.WellFounded using (Acc; acc)
open import Algebra.FunctionProperties using (Op₁)

module RoutingLib.Function.Metric {a} {ℓ} (S : Setoid a ℓ) where

  open Setoid S renaming (Carrier to A)

  MetricFunction : Set _
  MetricFunction = A → A → ℕ


  -- Predicates over distance functions

  Symmetric : Pred MetricFunction a
  Symmetric d = ∀ x y → d x y ≡ d y x
  
  TriangleIneq : Pred MetricFunction a
  TriangleIneq d = ∀ x y z → d x z ≤ d x y + d y z
    
  MaxTriangleIneq : Pred MetricFunction a
  MaxTriangleIneq d = ∀ x y z → d x z ≤ d x y ⊔ d y z

  Bounded : Pred MetricFunction a
  Bounded d = ∃ λ n → ∀ x y → d x y ≤ n

  -- Contractions
    
  _ContrOver_ : Op₁ A → MetricFunction → Set _
  f ContrOver d = ∀ x y → d (f x) (f y) ≤ d x y

  _StrContrOver_ : Op₁ A → MetricFunction → Set _
  f StrContrOver d = ∀ {x y} → ¬ (y ≈ x) → d (f x) (f y) < d x y

  _ContrOnOrbitsOver_ : Op₁ A → MetricFunction → Set _
  f ContrOnOrbitsOver d = ∀ x → d (f x) (f (f x)) ≤ d x (f x)

  _StrContrOnOrbitsOver_ : Op₁ A → MetricFunction → Set _
  f StrContrOnOrbitsOver d = ∀ {x} → ¬ (f x ≈ x) → d (f x) (f (f x)) < d x (f x)


  -- Balls

  -- x is in the ball of radius r around point y
  _∈[_∥_,_] : A → MetricFunction → A → ℕ → Set _
  x ∈[ d ∥ y , r ] = d x y ≤ r



  -- Types of distance spaces
  
  record IsMetric (d : MetricFunction) : Set (a ⊔ₗ ℓ) where
    field
      cong     : d Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
      eq⇒0     : ∀ {x y} → x ≈ y → d x y ≡ 0
      0⇒eq     : ∀ {x y} → d x y ≡ 0 → x ≈ y
      sym      : ∀ x y → d x y ≡ d y x
      triangle : TriangleIneq d

  record Metric : Set (a ⊔ₗ ℓ) where
    field
      d        : MetricFunction
      isMetric : IsMetric d

    open IsMetric isMetric public


  record IsUltrametric (d : A → A → ℕ) : Set (a ⊔ₗ ℓ) where
    field
      cong        : d Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
      eq⇒0        : ∀ {x y} → x ≈ y → d x y ≡ 0
      0⇒eq        : ∀ {x y} → d x y ≡ 0 → x ≈ y
      sym         : ∀ x y → d x y ≡ d y x
      maxTriangle : MaxTriangleIneq d

  record Ultrametric : Set (a ⊔ₗ ℓ) where
    field
      d : A → A → ℕ
      isUltrametric : IsUltrametric d

    open IsUltrametric isUltrametric public
