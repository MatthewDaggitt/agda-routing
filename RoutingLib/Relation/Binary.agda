open import Data.Product
open import Function using (flip)
open import Relation.Binary
open import Relation.Nullary using (¬_)
open import Level

module RoutingLib.Relation.Binary where

--------------------------------------------------------------------------------
-- Pairs of non-strict and strict partial orders

record IsOrderingPair
  {a ℓ₁ ℓ₂ ℓ₃} {A : Set a}
  (_≈_ : Rel A ℓ₁) (_≤_ : Rel A ℓ₂) (_<_ : Rel A ℓ₃)
  : Set (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where

  field
    isEquivalence : IsEquivalence _≈_
    isPartialOrder : IsPartialOrder _≈_ _≤_
    isStrictPartialOrder : IsStrictPartialOrder _≈_ _<_
    <⇒≤       : _<_ ⇒ _≤_
    ≤∧≉⇒<     : ∀ {x y} → x ≤ y → ¬ (x ≈ y) → x < y
    <-≤-trans : Trans _<_ _≤_ _<_
    ≤-<-trans : Trans _≤_ _<_ _<_

  module Eq = IsEquivalence isEquivalence
  module PO = IsPartialOrder isPartialOrder
  module SPO = IsStrictPartialOrder isStrictPartialOrder

  <-respʳ-≈ : _<_ Respectsʳ _≈_
  <-respʳ-≈ = proj₁ SPO.<-resp-≈

  <-respˡ-≈ : _<_ Respectsˡ _≈_
  <-respˡ-≈ = proj₂ SPO.<-resp-≈


record OrderingPair a ℓ₁ ℓ₂ ℓ₃ : Set (suc (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where

  field
    Carrier        : Set a
    _≈_            : Rel Carrier ℓ₁
    _≤_            : Rel Carrier ℓ₂
    _<_            : Rel Carrier ℓ₃
    isOrderingPair : IsOrderingPair _≈_ _≤_ _<_

  open IsOrderingPair isOrderingPair public

--------------------------------------------------------------------------------
-- Decidable preorders

record IsDecPreorder {a ℓ₁ ℓ₂} {A : Set a}
                       (_≈_ : Rel A ℓ₁) (_≤_ : Rel A ℓ₂) :
                       Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  infix 4 _≟_ _≤?_

  field
    isPreorder : IsPreorder _≈_ _≤_
    _≟_            : Decidable _≈_
    _≤?_           : Decidable _≤_

  private
    module PO = IsPreorder isPreorder
  open PO public hiding (module Eq)

  module Eq where

    isDecEquivalence : IsDecEquivalence _≈_
    isDecEquivalence = record
      { isEquivalence = PO.isEquivalence
      ; _≟_           = _≟_
      }

    open IsDecEquivalence isDecEquivalence public


record DecPreorder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where

  infix 4 _≈_ _≤_

  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ₁
    _≤_           : Rel Carrier ℓ₂
    isDecPreorder : IsDecPreorder _≈_ _≤_

  private
    module DPO = IsDecPreorder isDecPreorder
  open DPO public hiding (module Eq)

  preorder : Preorder c ℓ₁ ℓ₂
  preorder = record { isPreorder = isPreorder }

  module Eq where

    decSetoid : DecSetoid c ℓ₁
    decSetoid = record { isDecEquivalence = DPO.Eq.isDecEquivalence }

    open DecSetoid decSetoid public


record IsTotalPreorder {a ℓ₁ ℓ₂} {A : Set a}
                  (_≈_ : Rel A ℓ₁) (_≤_ : Rel A ℓ₂) :
                  Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPreorder : IsPreorder _≈_ _≤_
    total      : Total _≤_

  open IsPreorder isPreorder public


--------------------------------------------------------------------------------
-- Total preorders

record TotalPreorder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where

  infix 4 _≈_ _≤_

  field
    Carrier         : Set c
    _≈_             : Rel Carrier ℓ₁
    _≤_             : Rel Carrier ℓ₂
    isTotalPreorder : IsTotalPreorder _≈_ _≤_

  open IsTotalPreorder isTotalPreorder public

  preorder : Preorder c ℓ₁ ℓ₂
  preorder = record { isPreorder = isPreorder }


record IsDecTotalPreorder {a ℓ₁ ℓ₂} {A : Set a}
                       (_≈_ : Rel A ℓ₁) (_≤_ : Rel A ℓ₂) :
                       Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  infix 4 _≟_ _≤?_

  field
    isTotalPreorder : IsTotalPreorder _≈_ _≤_
    _≟_             : Decidable _≈_
    _≤?_            : Decidable _≤_

  private
    module TPO = IsTotalPreorder isTotalPreorder
  open TPO public hiding (module Eq)

  module Eq where

    isDecEquivalence : IsDecEquivalence _≈_
    isDecEquivalence = record
      { isEquivalence = TPO.isEquivalence
      ; _≟_           = _≟_
      }

    open IsDecEquivalence isDecEquivalence public

record DecTotalPreorder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where

  infix 4 _≈_ _≤_

  field
    Carrier            : Set c
    _≈_                : Rel Carrier ℓ₁
    _≤_                : Rel Carrier ℓ₂
    isDecTotalPreorder : IsDecTotalPreorder _≈_ _≤_

  private
    module DTPO = IsDecTotalPreorder isDecTotalPreorder
  open DTPO public hiding (module Eq)

  totalPreorder : TotalPreorder c ℓ₁ ℓ₂
  totalPreorder = record { isTotalPreorder = isTotalPreorder }

  module Eq where

    decSetoid : DecSetoid c ℓ₁
    decSetoid = record { isDecEquivalence = DTPO.Eq.isDecEquivalence }

    open DecSetoid decSetoid public
