open import Level using () renaming (_⊔_ to _⊔ₗ_)
open import Relation.Binary using (Setoid; Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_; yes; no)
open import Data.Nat using (ℕ; _≤_; _<_; _+_; _⊔_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import RoutingLib.Data.Nat.Properties using (⊔-sel; ≤-trans; m⊔n≤m+n)

module RoutingLib.Function.Metric {a} {ℓ} (S : Setoid a ℓ) where

  open Setoid S using (_≈_) renaming (Carrier to A)

  ------------------
  -- Inequalities --
  ------------------

  TriIneq : (A → A → ℕ) → Set a
  TriIneq d = ∀ x y z → d x z ≤ d x y + d y z

  StrongTriIneq : (A → A → ℕ) → Set a
  StrongTriIneq d = ∀ x y z → d x z ≤ d x y ⊔ d y z

  weaken : ∀ {d} → StrongTriIneq d → TriIneq d
  weaken {d} sti x y z = ≤-trans (sti x y z) (m⊔n≤m+n (d x y) (d y z))


  -------------
  -- Metrics --
  -------------

  record IsMetric (d : A → A → ℕ) : Set (a ⊔ₗ ℓ) where
    field
      eq⇨0 : ∀ {x y} → x ≈ y → d x y ≡ 0
      0⇨eq : ∀ {x y} → d x y ≡ 0 → x ≈ y
      sym : ∀ x y → d x y ≡ d y x
      triIneq : TriIneq d

  record Metric : Set (a ⊔ₗ ℓ) where
    field
      d : A → A → ℕ
      isMetric : IsMetric d

    open IsMetric isMetric public

  record IsUltrametric (d : A → A → ℕ) : Set (a ⊔ₗ ℓ) where
    field
      isMetric : IsMetric d
      strongTriIneq : StrongTriIneq d

    open IsMetric isMetric public

  record Ultrametric : Set (a ⊔ₗ ℓ) where
    field
      d : A → A → ℕ
      isUltrametric : IsUltrametric d

    open IsUltrametric isUltrametric public
