open import Data.Product using (_×_; _,_)
open import Function
open import Level using (Level; suc; _⊔_)
open import Relation.Binary using (Setoid; DecSetoid)
open import Relation.Binary.Indexed.Homogeneous
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary using (¬_; Dec)

open import RoutingLib.Relation.Unary.Indexed

module RoutingLib.Relation.Binary.Indexed.Homogeneous where

-------------------------------------------------------
-- At lemmas

Setoid_at_ : ∀ {i a ℓ} {I : Set i} → IndexedSetoid I a ℓ → I → Setoid a ℓ
Setoid S at i = record
  { Carrier       = Carrierᵢ i
  ; _≈_           = _≈ᵢ_
  ; isEquivalence = record
    { refl  = reflᵢ
    ; sym   = symᵢ
    ; trans = transᵢ
    }
  }
  where open IndexedSetoid S

triviallyIndexSetoid : ∀ {i a ℓ} (I : Set i) → Setoid a ℓ → IndexedSetoid I a ℓ
triviallyIndexSetoid I S = record
  { Carrierᵢ       = λ _ → Carrier
  ; _≈ᵢ_           = _≈_
  ; isEquivalenceᵢ = record
    { reflᵢ  = refl
    ; symᵢ   = sym
    ; transᵢ = trans
    }
  }
  where open Setoid S

triviallyIndexDecSetoid : ∀ {i a ℓ} (I : Set i) → DecSetoid a ℓ → IndexedDecSetoid I a ℓ
triviallyIndexDecSetoid I DS = record
  { isDecEquivalenceᵢ = record
    { _≟ᵢ_           = _≟_
    ; isEquivalenceᵢ = record
      { reflᵢ  = refl
      ; symᵢ   = sym
      ; transᵢ = trans
      }
    }
  }
  where open DecSetoid DS
