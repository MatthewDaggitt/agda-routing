
open import Relation.Binary
open import Relation.Binary.On using (decidable; total; isPreorder)
open import Function using (_on_)

open import RoutingLib.Relation.Binary

module RoutingLib.Relation.Binary.On where

module _ {a b} {A : Set a} {B : Set b} (f : B → A) where

  isTotalPreorder : ∀ {ℓ₁ ℓ₂} {≈ : Rel A ℓ₁} {≤ : Rel A ℓ₂} →
                    IsTotalPreorder ≈ ≤ →
                    IsTotalPreorder (≈ on f) (≤ on f)
  isTotalPreorder tp = record
    { isPreorder = isPreorder f (IsTotalPreorder.isPreorder tp)
    ; total      = total f _ (IsTotalPreorder.total tp)
    }

  isDecTotalPreorder : ∀ {ℓ₁ ℓ₂} {≈ : Rel A ℓ₁} {≤ : Rel A ℓ₂} →
                       IsDecTotalPreorder ≈ ≤ →
                       IsDecTotalPreorder (≈ on f) (≤ on f)
  isDecTotalPreorder D = record
    { isTotalPreorder = isTotalPreorder (IsDecTotalPreorder.isTotalPreorder D)
    ; _≟_             = decidable f _ (IsDecTotalPreorder._≟_ D)
    ; _≤?_            = decidable f _ (IsDecTotalPreorder._≤?_ D)
    }

totalPreorder : ∀ {a b ℓ₁ ℓ₂} {B : Set b} (D : TotalPreorder a ℓ₁ ℓ₂) →
                (B → TotalPreorder.Carrier D) → TotalPreorder b ℓ₁ ℓ₂
totalPreorder D f = record
  { isTotalPreorder = isTotalPreorder f (TotalPreorder.isTotalPreorder D)
  }

decTotalPreorder : ∀ {a b ℓ₁ ℓ₂} {B : Set b} (D : DecTotalPreorder a ℓ₁ ℓ₂) →
                   (B → DecTotalPreorder.Carrier D) → DecTotalPreorder b ℓ₁ ℓ₂
decTotalPreorder D f = record
  { isDecTotalPreorder = isDecTotalPreorder f (DecTotalPreorder.isDecTotalPreorder D)
  }
