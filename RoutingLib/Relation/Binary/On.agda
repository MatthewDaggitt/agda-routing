
open import Relation.Binary
open import Relation.Binary.On using (decidable; total; isPreorder)
open import Function using (_on_)

open import RoutingLib.Relation.Binary

module RoutingLib.Relation.Binary.On {a b} {A : Set a} {B : Set b} (f : B → A) where

  isTotalPreorder : ∀ {ℓ₁ ℓ₂} {≈ : Rel A ℓ₁} {≤ : Rel A ℓ₂} →
                      IsTotalPreorder ≈ ≤ →
                      IsTotalPreorder (≈ on f) (≤ on f)
  isTotalPreorder {≈ = ≈} {≤} tp = record {
      isPreorder = isPreorder f (IsTotalPreorder.isPreorder tp) ;
      total = total f ≤ (IsTotalPreorder.total tp)
    }

  isDecTotalPreorder : ∀ {ℓ₁ ℓ₂} {≈ : Rel A ℓ₁} {≤ : Rel A ℓ₂} →
                      IsDecTotalPreorder ≈ ≤ →
                      IsDecTotalPreorder (≈ on f) (≤ on f)
  isDecTotalPreorder {≈ = ≈} {≤} dtp = record {
      isTotalPreorder = isTotalPreorder (IsDecTotalPreorder.isTotalPreorder dtp) ;
      _≟_ = decidable f ≈ (IsDecTotalPreorder._≟_ dtp);
      _≤?_ = decidable f ≤ (IsDecTotalPreorder._≤?_ dtp)
    }

