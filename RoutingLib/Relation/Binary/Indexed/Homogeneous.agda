open import Data.Product using (_×_; _,_)
open import Function
open import Level using (Level; suc; _⊔_)
import Relation.Binary as B
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary using (¬_; Dec)

open import RoutingLib.Relation.Unary.Indexed

module RoutingLib.Relation.Binary.Indexed.Homogeneous where

------------------------------------------------------------------------
-- Types

-- Heterogenous, homogenously-indexed relations

IREL : ∀ {i a₁ a₂} {I : Set i} → (I → Set a₁) → (I → Set a₂) → (ℓ : Level) → Set _
IREL A₁ A₂ ℓ = ∀ {i} → A₁ i → A₂ i → Set ℓ

-- Homogeneous, homogenously-indexed relations

IRel : ∀ {i a} {I : Set i} → (I → Set a) → (ℓ : Level) → Set _
IRel A = IREL A A

------------------------------------------------------------------------
-- Lifting to non-indexed relations

Lift : ∀ {i a ℓ} {I : Set i} (A : I → Set a) → IRel A ℓ → B.Rel (∀ i → A i) _
Lift A _∼_ x y = ∀ i → x i ∼ y i

------------------------------------------------------------------------
-- Properties

private
  Implies : ∀ {i a ℓ₁ ℓ₂} {I : Set i} (A : I → Set a) → IRel A ℓ₁ → IRel A ℓ₂ → Set _
  Implies A _∼₁_ _∼₂_ = ∀ {i} → (_∼₁_ {i}) B.⇒ (_∼₂_ {i})

syntax Implies A _∼₁_ _∼₂_ = _∼₁_ ⇒[ A ] _∼₂_

Reflexive : ∀ {i a ℓ} {I : Set i} (A : I → Set a) → IRel A ℓ → Set _
Reflexive _ _∼_ = ∀ {i} → B.Reflexive (_∼_ {i})

Symmetric : ∀ {i a ℓ} {I : Set i} (A : I → Set a) → IRel A ℓ → Set _
Symmetric _ _∼_ = ∀ {i} → B.Symmetric (_∼_ {i})

Transitive : ∀ {i a ℓ} {I : Set i} (A : I → Set a) → IRel A ℓ → Set _
Transitive _ _∼_ = ∀ {i} → B.Transitive (_∼_ {i})

Antisymmetric : ∀ {i a ℓ₁ ℓ₂} {I : Set i} (A : I → Set a) → IRel A ℓ₁ → IRel A ℓ₂ → Set _
Antisymmetric _ _≈_ _∼_ = ∀ {i} → B.Antisymmetric (_≈_ {i}) (_∼_ {i})

Decidable : ∀ {i a ℓ} {I : Set i} (A : I → Set a) → IRel A ℓ → Set _
Decidable A _∼_ = ∀ {i} → B.Decidable (_∼_ {i})

Respects : ∀ {i a ℓ₁ ℓ₂} {I : Set i} (A : I → Set a) → IPred A ℓ₁ → IRel A ℓ₂ → Set _
Respects A P _∼_ = ∀ {i} {x y : A i} → x ∼ y → P x → P y

Respectsˡ : ∀ {i a ℓ₁ ℓ₂} {I : Set i} (A : I → Set a) → IRel A ℓ₁ → IRel A ℓ₂ → Set _
Respectsˡ A P _∼_  = ∀ {i} {x y z : A i} → x ∼ y → P x z → P y z

Respectsʳ : ∀ {i a ℓ₁ ℓ₂} {I : Set i} (A : I → Set a) → IRel A ℓ₁ → IRel A ℓ₂ → Set _
Respectsʳ A P _∼_ = ∀ {i} {x y z : A i} → x ∼ y → P z x → P z y

Respects₂ : ∀ {i a ℓ₁ ℓ₂} {I : Set i} (A : I → Set a) → IRel A ℓ₁ → IRel A ℓ₂ → Set _
Respects₂ A P _∼_ = (Respectsʳ A P _∼_) × (Respectsˡ A P _∼_)

{-
Preserves : ∀ {i a b ℓ₁ ℓ₂} {I : Set i} (A : I → Set a) {B : I → Set b} →
                (∀ {i} → A i → B i) → Rel A ℓ₁ → Rel B ℓ₂ → Set _
Preserves A f P Q = ∀ {i} {x y : A i} → P x y → Q (f x) (f y)
-}

------------------------------------------------------------------------
-- Records

record IsIndexedEquivalence {i a ℓ} {I : Set i} (A : I → Set a)
                     (_≈ᵢ_ : IRel A ℓ) : Set (i ⊔ a ⊔ ℓ) where
  field
    reflᵢ  : Reflexive A _≈ᵢ_
    symᵢ   : Symmetric A _≈ᵢ_
    transᵢ : Transitive A _≈ᵢ_

  reflexiveᵢ : ∀ {i} → _≡_ ⟨ B._⇒_ ⟩ _≈ᵢ_ {i}
  reflexiveᵢ P.refl = reflᵢ

  -- Lift properties

  reflexive : _≡_ B.⇒ (Lift A _≈ᵢ_)
  reflexive P.refl i = reflᵢ

  refl : B.Reflexive (Lift A _≈ᵢ_)
  refl i = reflᵢ

  sym : B.Symmetric (Lift A _≈ᵢ_)
  sym x≈y i = symᵢ (x≈y i)

  trans : B.Transitive (Lift A _≈ᵢ_)
  trans x≈y y≈z i = transᵢ (x≈y i) (y≈z i)

  isEquivalence : B.IsEquivalence (Lift A _≈ᵢ_)
  isEquivalence = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }


record IndexedSetoid {i} (I : Set i) c ℓ : Set (suc (i ⊔ c ⊔ ℓ)) where
  infix 4 _≈ᵢ_ _≈_
  field
    Carrierᵢ       : I → Set c
    _≈ᵢ_           : IRel Carrierᵢ ℓ
    isEquivalenceᵢ : IsIndexedEquivalence Carrierᵢ _≈ᵢ_

  open IsIndexedEquivalence isEquivalenceᵢ public

  Carrier : Set _
  Carrier = ∀ i → Carrierᵢ i

  _≈_ : B.Rel Carrier _
  _≈_ = Lift Carrierᵢ _≈ᵢ_

  setoid : B.Setoid _ _
  setoid = record
    { isEquivalence = isEquivalence
    }


record IsIndexedDecEquivalence {i a ℓ} {I : Set i} (A : I → Set a)
                               (_≈ᵢ_ : IRel A ℓ) : Set (i ⊔ a ⊔ ℓ) where
  infix 4 _≟ᵢ_
  field
    _≟ᵢ_           : Decidable A _≈ᵢ_
    isEquivalenceᵢ : IsIndexedEquivalence A _≈ᵢ_
  
record IndexedDecSetoid {i} (I : Set i) c ℓ : Set (suc (i ⊔ c ⊔ ℓ)) where
  infix 4 _≈ᵢ_
  field
    Carrierᵢ          : I → Set c
    _≈ᵢ_              : IRel Carrierᵢ ℓ
    isDecEquivalenceᵢ : IsIndexedDecEquivalence Carrierᵢ _≈ᵢ_

  open IsIndexedDecEquivalence isDecEquivalenceᵢ public

  indexedSetoid : IndexedSetoid I c ℓ
  indexedSetoid = record { isEquivalenceᵢ = isEquivalenceᵢ }


record IsIndexedPreorder {i a ℓ₁ ℓ₂} {I : Set i} (A : I → Set a)
                  (_≈ᵢ_ : IRel A ℓ₁) (_∼ᵢ_ : IRel A ℓ₂) : Set (i ⊔ a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isEquivalenceᵢ : IsIndexedEquivalence A _≈ᵢ_
    reflexiveᵢ     : _≈ᵢ_ ⇒[ A ] _∼ᵢ_
    transᵢ         : Transitive A _∼ᵢ_

  module Eq = IsIndexedEquivalence isEquivalenceᵢ

  reflᵢ : Reflexive A _∼ᵢ_
  reflᵢ = reflexiveᵢ Eq.reflᵢ

  ∼ᵢ-respˡ-≈ᵢ : Respectsˡ A _∼ᵢ_ _≈ᵢ_
  ∼ᵢ-respˡ-≈ᵢ x≈y x∼z = transᵢ (reflexiveᵢ (Eq.symᵢ x≈y)) x∼z

  ∼ᵢ-respʳ-≈ᵢ : Respectsʳ A _∼ᵢ_ _≈ᵢ_
  ∼ᵢ-respʳ-≈ᵢ x≈y z∼x = transᵢ z∼x (reflexiveᵢ x≈y)

  ∼ᵢ-resp-≈ᵢ : Respects₂ A _∼ᵢ_ _≈ᵢ_
  ∼ᵢ-resp-≈ᵢ = ∼ᵢ-respʳ-≈ᵢ , ∼ᵢ-respˡ-≈ᵢ



  reflexive : Lift A _≈ᵢ_ B.⇒ Lift A _∼ᵢ_
  reflexive x≈y i = reflexiveᵢ (x≈y i)

  refl : B.Reflexive (Lift A _∼ᵢ_)
  refl i = reflᵢ

  trans : B.Transitive (Lift A _∼ᵢ_)
  trans x≈y y≈z i = transᵢ (x≈y i) (y≈z i)

  ∼-respˡ-≈ : (Lift A _∼ᵢ_) B.Respectsˡ (Lift A _≈ᵢ_)
  ∼-respˡ-≈ x≈y x∼z i = ∼ᵢ-respˡ-≈ᵢ (x≈y i) (x∼z i)

  ∼-respʳ-≈ : (Lift A _∼ᵢ_) B.Respectsʳ (Lift A _≈ᵢ_)
  ∼-respʳ-≈ x≈y z∼x i = ∼ᵢ-respʳ-≈ᵢ (x≈y i) (z∼x i)

  ∼-resp-≈ : (Lift A _∼ᵢ_) B.Respects₂ (Lift A _≈ᵢ_)
  ∼-resp-≈ = ∼-respʳ-≈ , ∼-respˡ-≈

  isPreorder : B.IsPreorder (Lift A _≈ᵢ_) (Lift A _∼ᵢ_)
  isPreorder = record
    { isEquivalence = Eq.isEquivalence
    ; reflexive     = reflexive
    ; trans         = trans
    }

record IndexedPreorder {i} (I : Set i) c ℓ : Set (suc (i ⊔ c ⊔ ℓ)) where

  infix 4 _≈ᵢ_ _∼ᵢ_ _≈_ _∼_

  field
    Carrierᵢ    : I → Set c
    _≈ᵢ_        : IRel Carrierᵢ ℓ
    _∼ᵢ_        : IRel Carrierᵢ ℓ
    isPreorderᵢ : IsIndexedPreorder Carrierᵢ _≈ᵢ_ _∼ᵢ_

  open IsIndexedPreorder isPreorderᵢ public

  Carrier : Set _
  Carrier = ∀ i → Carrierᵢ i

  _≈_ : B.Rel Carrier _
  x ≈ y = ∀ i → x i ≈ᵢ y i

  _∼_ : B.Rel Carrier _
  x ∼ y = ∀ i → x i ∼ᵢ y i

  preorder : B.Preorder _ _ _
  preorder = record { isPreorder = isPreorder }

record IsIndexedPartialOrder {i a ℓ₁ ℓ₂} {I : Set i} (A : I → Set a)
                      (_≈ᵢ_ : IRel A ℓ₁) (_≤ᵢ_ : IRel A ℓ₂) : Set (i ⊔ a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPreorderᵢ : IsIndexedPreorder A _≈ᵢ_ _≤ᵢ_
    antisymᵢ    : Antisymmetric A _≈ᵢ_ _≤ᵢ_

  open IsIndexedPreorder isPreorderᵢ public
    renaming
    ( ∼ᵢ-respˡ-≈ᵢ to ≤ᵢ-respˡ-≈ᵢ
    ; ∼ᵢ-respʳ-≈ᵢ to ≤ᵢ-respʳ-≈ᵢ
    ; ∼ᵢ-resp-≈ᵢ  to ≤ᵢ-resp-≈ᵢ
    ; ∼-respˡ-≈   to ≤-respˡ-≈
    ; ∼-respʳ-≈   to ≤-respʳ-≈
    ; ∼-resp-≈    to ≤-resp-≈
    )

  antisym : B.Antisymmetric (Lift A _≈ᵢ_) (Lift A _≤ᵢ_)
  antisym x≤y y≤x i = antisymᵢ (x≤y i) (y≤x i)

  isPartialOrder : B.IsPartialOrder (Lift A _≈ᵢ_) (Lift A _≤ᵢ_)
  isPartialOrder = record
    { isPreorder = isPreorder
    ; antisym    = antisym
    }

record IndexedPoset {i} (I : Set i) c ℓ : Set (suc (i ⊔ c ⊔ ℓ)) where

  field
    Carrierᵢ        : I → Set c
    _≈ᵢ_            : IRel Carrierᵢ ℓ
    _≤ᵢ_            : IRel Carrierᵢ ℓ
    isPartialOrderᵢ : IsIndexedPartialOrder Carrierᵢ _≈ᵢ_ _≤ᵢ_

  open IsIndexedPartialOrder isPartialOrderᵢ public

  preorderᵢ : IndexedPreorder _ _ _
  preorderᵢ = record { isPreorderᵢ = isPreorderᵢ }

  open IndexedPreorder preorderᵢ public
    using (Carrier; _≈_)
    renaming (_∼_ to _≤_)

  poset : B.Poset _ _ _
  poset = record { isPartialOrder = isPartialOrder }

-------------------------------------------------------
-- At lemmas

Setoid_at_ : ∀ {i a ℓ} {I : Set i} → IndexedSetoid I a ℓ → I → B.Setoid _ _
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

triviallyIndexSetoid : ∀ {i a ℓ} → (I : Set i) →  B.Setoid a ℓ → IndexedSetoid I a ℓ
triviallyIndexSetoid I S = record
  { Carrierᵢ       = λ _ → Carrier
  ; _≈ᵢ_           = _≈_
  ; isEquivalenceᵢ = record
    { reflᵢ  = refl
    ; symᵢ   = sym
    ; transᵢ = trans
    }
  }
  where open B.Setoid S
