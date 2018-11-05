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

infix 4 _≤_

_≤_ : Rel A ℓ
x ≤ y = (y ∙ x) ≈ x

-- Properties

reflexive : IsEquivalence _≈_ → Congruent₂ _∙_ → Idempotent _∙_ → _≈_ ⇒ _≤_
reflexive isEq cong idem x≈y = trans (cong (sym x≈y) refl) (idem _)
  where open IsEquivalence isEq

refl : Idempotent _∙_ → Reflexive _≤_
refl idem {x} = idem x

antisym : IsEquivalence _≈_ → Commutative _∙_ → Antisymmetric _≈_ _≤_
antisym isEq comm {x} {y} x≤y y≤x = trans (trans (sym x≤y) (comm y x)) y≤x
  where open IsEquivalence isEq

total : Transitive _≈_ → Selective _∙_ → Commutative _∙_ → Total _≤_
total trans sel comm x y with sel x y
... | inj₁ x∙y≈x = inj₁ (trans (comm y x) x∙y≈x)
... | inj₂ x∙y≈y = inj₂ x∙y≈y

trans : IsSemigroup _≈_ _∙_ → Transitive _≤_
trans semi {x} {y} {z} x≤y y≤z = begin
  z ∙ x       ≈⟨ ∙-cong ≈-refl (sym x≤y) ⟩
  z ∙ (y ∙ x) ≈⟨ sym (assoc z y x) ⟩
  (z ∙ y) ∙ x ≈⟨ ∙-cong y≤z ≈-refl ⟩
  y ∙ x       ≈⟨ x≤y ⟩
  x           ∎
  where
  open IsSemigroup semi renaming (refl to ≈-refl)
  open EqReasoning setoid

respʳ : IsEquivalence _≈_ → Congruent₂ _∙_ → _≤_ Respectsʳ _≈_
respʳ isEq cong x≈y x≤z = Eq.trans (cong (Eq.sym x≈y) Eq.refl) x≤z
  where module Eq = IsEquivalence isEq

respˡ : IsEquivalence _≈_ → Congruent₂ _∙_ → _≤_ Respectsˡ _≈_
respˡ isEq cong z≈x z≤y = Eq.trans (Eq.trans (cong Eq.refl (Eq.sym z≈x)) z≤y) z≈x
  where module Eq = IsEquivalence isEq

resp₂ : IsEquivalence _≈_ → Congruent₂ _∙_ →  _≤_ Respects₂ _≈_
resp₂ isEq cong = respʳ isEq cong , respˡ isEq cong

dec : Decidable _≈_ → Decidable _≤_
dec dec x y = dec (y ∙ x) x

isPreorder : IsBand _≈_ _∙_ → IsPreorder _≈_ _≤_
isPreorder band = record
  { isEquivalence = isEquivalence
  ; reflexive     = reflexive isEquivalence ∙-cong idem
  ; trans         = trans isSemigroup
  }
  where open IsBand band hiding (reflexive; trans)

isPartialOrder : IsSemilattice _≈_ _∙_ → IsPartialOrder _≈_ _≤_
isPartialOrder semilattice = record
  { isPreorder = isPreorder isBand
  ; antisym    = antisym isEquivalence comm
  }
  where open IsSemilattice semilattice

isDecPartialOrder : IsSemilattice _≈_ _∙_ → Decidable _≈_ → IsDecPartialOrder _≈_ _≤_
isDecPartialOrder semilattice _≟_ = record
  { isPartialOrder = isPartialOrder semilattice
  ; _≟_            = _≟_
  ; _≤?_           = dec _≟_
  }

isTotalOrder : IsSemilattice _≈_ _∙_ → Selective _∙_ → IsTotalOrder _≈_ _≤_
isTotalOrder latt sel  = record
  { isPartialOrder = isPartialOrder latt
  ; total          = total ≈-trans sel comm
  }
  where open IsSemilattice latt renaming (trans to ≈-trans)

isDecTotalOrder : IsSemilattice _≈_ _∙_ → Selective _∙_ →
                  Decidable _≈_ → IsDecTotalOrder _≈_ _≤_
isDecTotalOrder latt sel _≟_ = record
  { isTotalOrder = isTotalOrder latt sel
  ; _≟_          = _≟_
  ; _≤?_         = dec _≟_
  }

preorder : IsBand _≈_ _∙_ → Preorder a ℓ ℓ
preorder band = record
  { isPreorder = isPreorder band
  }

poset : IsSemilattice _≈_ _∙_ → Poset a ℓ ℓ
poset semilattice = record
  { isPartialOrder = isPartialOrder semilattice
  }

decPoset : IsSemilattice _≈_ _∙_ → Decidable _≈_ → DecPoset a ℓ ℓ
decPoset semilattice dec = record
  { isDecPartialOrder = isDecPartialOrder semilattice dec
  }

totalOrder : IsSemilattice _≈_ _∙_ → Selective _∙_ → TotalOrder a ℓ ℓ
totalOrder latt sel = record
  { isTotalOrder = isTotalOrder latt sel
  }

decTotalOrder : IsSemilattice _≈_ _∙_ → Selective _∙_ →
                Decidable _≈_ → DecTotalOrder a ℓ ℓ
decTotalOrder latt sel dec = record
  { isDecTotalOrder = isDecTotalOrder latt sel dec
  }
