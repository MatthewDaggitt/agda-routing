open import Data.Product using (_,_; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary
open import Relation.Nullary using (¬_)
open import Algebra.FunctionProperties using (Op₂)
open import Algebra.Structures
import Relation.Binary.EqReasoning as EqReasoning

module RoutingLib.Relation.Binary.Construct.NaturalOrder.Right
  {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) (_∙_ : Op₂ A) where

  -- All added to standard library

  open import Algebra.FunctionProperties _≈_

  sel⇒idem : Selective _∙_ → Idempotent _∙_
  sel⇒idem sel x with sel x x
  ... | inj₁ x∙x≈x = x∙x≈x
  ... | inj₂ x∙x≈x = x∙x≈x

  -------------------------
  -- Right natural order --
  -------------------------

  infix 4 _≤_ _≰_ _<_ _≮_

  _≤_ : Rel A ℓ
  x ≤ y = (y ∙ x) ≈ x

  _≰_ : Rel A ℓ
  x ≰ y = ¬ (x ≤ y)

  _<_ : Rel A ℓ
  x < y = x ≤ y × ¬ (x ≈ y)

  _≮_ : Rel A ℓ
  x ≮ y = ¬ (x < y)

  -- Properties

  ≤-reflexive : IsEquivalence _≈_ → Congruent₂ _∙_ → Idempotent _∙_ → _≈_ ⇒ _≤_
  ≤-reflexive isEq cong idem x≈y = trans (cong (sym x≈y) refl) (idem _)
    where open IsEquivalence isEq

  ≤-refl : Idempotent _∙_ → Reflexive _≤_
  ≤-refl idem {x} = idem x

  ≤-antisym : IsEquivalence _≈_ → Commutative _∙_ → Antisymmetric _≈_ _≤_
  ≤-antisym isEq comm {x} {y} x≤y y≤x = trans (trans (sym x≤y) (comm y x)) y≤x
    where open IsEquivalence isEq

  ≤-total : Transitive _≈_ → Selective _∙_ → Commutative _∙_ → Total _≤_
  ≤-total trans sel comm x y with sel x y
  ... | inj₁ x∙y≈x = inj₁ (trans (comm y x) x∙y≈x)
  ... | inj₂ x∙y≈y = inj₂ x∙y≈y

  ≤-trans : IsSemigroup _≈_ _∙_ → Transitive _≤_
  ≤-trans semi {x} {y} {z} x≤y y≤z = begin
    z ∙ x       ≈⟨ ∙-cong refl (sym x≤y) ⟩
    z ∙ (y ∙ x) ≈⟨ sym (assoc z y x) ⟩
    (z ∙ y) ∙ x ≈⟨ ∙-cong y≤z refl ⟩
    y ∙ x       ≈⟨ x≤y ⟩
    x           ∎
    where
    open IsSemigroup semi
    open EqReasoning (record { isEquivalence = isEquivalence })

  ≤-respʳ-≈ : IsEquivalence _≈_ → Congruent₂ _∙_ → ∀ {x} → (x ≤_) Respects _≈_
  ≤-respʳ-≈ isEq cong x≈y x≤z = trans (cong (sym x≈y) refl) x≤z
    where open IsEquivalence isEq

  ≤-respₗ-≈ : IsEquivalence _≈_ → Congruent₂ _∙_ → ∀ {x} → (_≤ x) Respects _≈_
  ≤-respₗ-≈ isEq cong z≈x z≤y = trans (trans (cong refl (sym z≈x)) z≤y) z≈x
    where open IsEquivalence isEq

  ≤-resp₂-≈ : IsEquivalence _≈_ → Congruent₂ _∙_ →  _≤_ Respects₂ _≈_
  ≤-resp₂-≈ isEq cong = ≤-respʳ-≈ isEq cong , ≤-respₗ-≈ isEq cong

{-
  ≤-absₗ : Associative _∙_ → Idempotent _∙_ → ∀ x y → x ∙ y ≤ x
  ≤-absₗ assoc idem x y = {!!} --trans (sym (assoc x x y)) (pres (idem x) refl)

  ≤-abs : Commutative _∙_ → Associative _∙_ → Idempotent _∙_ → ∀ x y → y ∙ x ≤ x
  ≤-abs comm assoc idem x y = {!!} --trans (trans (trans (sym (assoc x y x)) (pres (comm x y) refl)) (assoc y x x)) (pres refl (idem x))
-}

  ≤-dec : Decidable _≈_ → Decidable _≤_
  ≤-dec dec x y = dec (y ∙ x) x

  ≤-isPreorder : IsSemigroup _≈_ _∙_ → Idempotent _∙_ → IsPreorder _≈_ _≤_
  ≤-isPreorder semi idem = record
    { isEquivalence = isEquivalence
    ; reflexive     = ≤-reflexive isEquivalence ∙-cong idem
    ; trans         = ≤-trans semi
    }
    where open IsSemigroup semi

  ≤-preorder : IsSemigroup _≈_ _∙_ → Idempotent _∙_ → Preorder a ℓ ℓ
  ≤-preorder assoc idem = record
    { Carrier = A
    ; _≈_ = _≈_
    ; _∼_ = _≤_
    ; isPreorder = ≤-isPreorder assoc idem
    }

  ≤-isPartialOrder : IsSemigroup _≈_ _∙_ → Commutative _∙_ →
                     Idempotent _∙_ → IsPartialOrder _≈_ _≤_
  ≤-isPartialOrder semi comm idem = record
    { isPreorder = ≤-isPreorder semi idem
    ; antisym    = ≤-antisym isEquivalence comm
    }
    where open IsSemigroup semi

  ≤-poset : IsSemigroup _≈_ _∙_ → Commutative _∙_ → Idempotent _∙_ →  Poset a ℓ ℓ
  ≤-poset semi comm idem = record
    { Carrier = A
    ; _≈_ = _≈_
    ; _≤_ = _≤_
    ; isPartialOrder = ≤-isPartialOrder semi comm idem
    }

  ≤-isDecPartialOrder : IsSemigroup _≈_ _∙_ → Decidable _≈_ →
                        Commutative _∙_ → Idempotent _∙_ → IsDecPartialOrder _≈_ _≤_
  ≤-isDecPartialOrder semi dec comm idem = record
    { isPartialOrder = ≤-isPartialOrder semi comm idem
    ; _≟_ = dec
    ; _≤?_ = ≤-dec dec
    }

  ≤-decPoset : IsSemigroup _≈_ _∙_ → Decidable _≈_ → Commutative _∙_ →
               Idempotent _∙_ → DecPoset a ℓ ℓ
  ≤-decPoset semi dec comm idem = record {
      Carrier = A ;
      _≈_ = _≈_ ;
      _≤_ = _≤_ ;
      isDecPartialOrder = ≤-isDecPartialOrder semi dec comm idem
    }

  ≤-isTotalOrder : IsSemigroup _≈_ _∙_ → Commutative _∙_ →
                   Selective _∙_ → IsTotalOrder _≈_ _≤_
  ≤-isTotalOrder semi comm sel  = record
    { isPartialOrder = ≤-isPartialOrder semi comm (sel⇒idem sel)
    ; total = ≤-total trans sel comm
    }
    where open IsSemigroup semi

  ≤-totalOrder : IsSemigroup _≈_ _∙_ → Commutative _∙_ →
                 Selective _∙_ → TotalOrder a ℓ ℓ
  ≤-totalOrder semi comm sel = record
    { Carrier = A
    ; _≈_     = _≈_
    ; _≤_     = _≤_
    ; isTotalOrder = ≤-isTotalOrder semi comm sel
    }

  ≤-isDecTotalOrder : IsSemigroup _≈_ _∙_ → Decidable _≈_ → Commutative _∙_ →
                      Selective _∙_ → IsDecTotalOrder _≈_ _≤_
  ≤-isDecTotalOrder semi dec comm sel = record
    { isTotalOrder = ≤-isTotalOrder semi comm sel
    ; _≟_          = dec
    ; _≤?_         = ≤-dec dec
    }

  ≤-decTotalOrder : IsSemigroup _≈_ _∙_ → Decidable _≈_ → Commutative _∙_ →
                    Selective _∙_ → DecTotalOrder a ℓ ℓ
  ≤-decTotalOrder semi dec comm sel = record
    { Carrier = A
    ; _≈_ = _≈_
    ; _≤_ = _≤_
    ; isDecTotalOrder = ≤-isDecTotalOrder semi dec comm sel
    }
