open import Algebra

module db716.Algebra.Properties.Semigroup {c ℓ} (S : Semigroup c ℓ) where
  open Semigroup S renaming (Carrier to C)

  open import Relation.Binary
  open import Algebra.FunctionProperties _≈_
  open import Relation.Binary.EqReasoning setoid
  open import Data.Sum
  open import db716.Relation.Binary.NaturalOrder _≈_ _∙_

  comm⇒asymᴸ : Commutative _∙_ → Antisymmetric _≈_ _≤ᴸ_
  comm⇒asymᴸ comm {x} {y} (x≤ᴸy) (y≤ᴸx) = begin
    x     ≈⟨ sym x≤ᴸy ⟩
    x ∙ y ≈⟨ comm x y ⟩
    y ∙ x ≈⟨ y≤ᴸx ⟩
    y     ∎

  comm⇒asymᴿ : Commutative _∙_ → Antisymmetric _≈_ _≤ᴿ_
  comm⇒asymᴿ comm {x} {y} (x≤ᴿy) (y≤ᴿx) = begin
    x     ≈⟨ sym x≤ᴿy ⟩
    y ∙ x ≈⟨ comm y x ⟩
    x ∙ y ≈⟨ y≤ᴿx ⟩
    y     ∎

  assoc⇒transᴸ : Associative _∙_ → Transitive _≤ᴸ_
  assoc⇒transᴸ assoc {x} {y} {z} (x≤ᴸy) (y≤ᴸz) = begin
    x ∙ z       ≈⟨ ∙-cong (sym x≤ᴸy) refl ⟩
    (x ∙ y) ∙ z ≈⟨ assoc x y z ⟩
    x ∙ (y ∙ z) ≈⟨ ∙-cong refl y≤ᴸz ⟩
    x ∙ y       ≈⟨ x≤ᴸy ⟩
    x           ∎

  assoc⇒transᴿ : Associative _∙_ → Transitive _≤ᴿ_
  assoc⇒transᴿ assoc {x} {y} {z} (x≤ᴿy) (y≤ᴿz) = begin
    z ∙ x       ≈⟨ ∙-cong refl (sym x≤ᴿy) ⟩
    z ∙ (y ∙ x) ≈⟨ sym (assoc z y x) ⟩
    (z ∙ y) ∙ x ≈⟨ ∙-cong y≤ᴿz refl ⟩
    y ∙ x       ≈⟨ x≤ᴿy ⟩
    x           ∎

  comm+sel⇒totalᴸ : Commutative _∙_ → Selective _∙_ → Total _≤ᴸ_
  comm+sel⇒totalᴸ comm sel x y with (sel x y)
  ... | inj₁ x∙y≈x = inj₁ x∙y≈x
  ... | inj₂ x∙y≈y = inj₂ (begin
    y ∙ x ≈⟨ comm y x ⟩
    x ∙ y ≈⟨ x∙y≈y ⟩
    y     ∎)

  comm+sel⇒totalᴿ : Commutative _∙_ → Selective _∙_ → Total _≤ᴿ_
  comm+sel⇒totalᴿ comm sel x y with (sel x y)
  ... | inj₁ x∙y≈x = inj₁ (begin
    y ∙ x ≈⟨ comm y x ⟩
    x ∙ y ≈⟨ x∙y≈x ⟩
    x     ∎)
  ... | inj₂ x∙y≈y = inj₂ x∙y≈y

  comm+totalᴸ⇒sel : Commutative _∙_ → Total _≤ᴸ_ → Selective _∙_
  comm+totalᴸ⇒sel comm total x y with (total x y)
  ... | inj₁ x≤ᴸy = inj₁ x≤ᴸy
  ... | inj₂ y≤ᴸx = inj₂ (begin
    x ∙ y ≈⟨ comm x y ⟩
    y ∙ x ≈⟨ y≤ᴸx ⟩
    y     ∎)

  comm+totalᴿ⇒sel : Commutative _∙_ → Total _≤ᴿ_ → Selective _∙_
  comm+totalᴿ⇒sel comm total x y with (total x y)
  ... | inj₁ x≤ᴿy = inj₁ (begin
    x ∙ y ≈⟨ comm x y ⟩
    y ∙ x ≈⟨ x≤ᴿy ⟩
    x     ∎)
  ... | inj₂ y≤ᴿx = inj₂ y≤ᴿx
    
