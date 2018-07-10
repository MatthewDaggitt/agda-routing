open import Level using () renaming (_⊔_ to _⊔ₗ_)
open import Relation.Binary using (Setoid; Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_; yes; no)
open import Data.Nat using (ℕ; _≤_; _<_; _+_; _⊔_)
open import Data.Nat.Properties using (⊔-sel)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import RoutingLib.Data.Nat.Properties using (≤-trans; m⊔n≤m+n)

module RoutingLib.Function.Metric.Ultrametric {a} {ℓ} (S : Setoid a ℓ) where

  --open Setoid S using (_≈_) renaming (Carrier to A)
  --open import RoutingLib.Function.Metric S using (TriIneq; IsMetric)

  open import RoutingLib.Function.Metric



  replace-equality : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} {_≈₁_ : Rel A ℓ₁} {_\ → IsUltrametric S₁ {!!} → IsUltrametric S₂ {!!}
  replace-equality = {!!}


  ------------------
  -- Ultrametrics --
  ------------------

