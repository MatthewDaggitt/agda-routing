open import Algebra.FunctionProperties using (Op₂; Idempotent)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (_⊔_)
open import Relation.Binary using (Rel; Transitive; Symmetric; Decidable)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Algebra.FunctionProperties using (Selective)

module RoutingLib.Algebra.Selectivity.Properties {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) (_•_ : Op₂ A) (sel : Selective _≈_ _•_) where

  private
    infix 4 _≉_

    _≉_ : Rel A ℓ
    x ≉ y = ¬ (x ≈ y)


  idem : Idempotent _≈_ _•_
  idem a with sel a a
  ... | inj₁ a•a≈a = a•a≈a
  ... | inj₂ a•a≈a = a•a≈a

  excluded-middle-left : ∀ {x y} → x • y ≉ x → (x • y) ≈ y
  excluded-middle-left {x} {y} x•y≉x with sel x y
  ... | inj₁ x•y≈x = contradiction x•y≈x x•y≉x
  ... | inj₂ x•y≈y = x•y≈y

  excluded-middle-right : ∀ {x y} → x • y ≉ y → (x • y) ≈ x
  excluded-middle-right {x} {y} x•y≉y with sel x y
  ... | inj₁ x•y≈x = x•y≈x
  ... | inj₂ x•y≈y = contradiction x•y≈y x•y≉y

  selective-equality : Transitive _≈_ → ∀ {x y v} → v ≈ (x • y) → (v ≈ x) ⊎ (v ≈ y)
  selective-equality trans {x} {y} {v} v≈x•y with sel x y
  ... | inj₁ x•y≈x = inj₁ (trans v≈x•y x•y≈x)
  ... | inj₂ x•y≈y = inj₂ (trans v≈x•y x•y≈y)
  
  selective-inequality : Transitive _≈_ → ∀ {x y v} → v ≉ x → v ≉ y → v ≉ x • y
  selective-inequality trans {x} {y} {v} v≉x v≉y v≈x•y with sel x y
  ... | inj₁ x•y≈x = v≉x (trans v≈x•y x•y≈x)
  ... | inj₂ x•y≈y = v≉y (trans v≈x•y x•y≈y)


  -----------
  -- Other --
  -----------

  data SelCase : A → A → Set (a ⊔ ℓ) where
    sel₁ : ∀ {x y} → (x • y) ≈ x → (x • y) ≉ y → SelCase x y
    sel₂ : ∀ {x y} → (x • y) ≉ x → (x • y) ≈ y → SelCase x y
    sel≈ : ∀ {x y} → (x • y) ≈ x → (x • y) ≈ y → SelCase x y

  selection : Symmetric _≈_ → Transitive _≈_ → Decidable _≈_ → ∀ x y → SelCase x y
  selection sym trans _≟_ x y with sel x y | x ≟ y
  ... | inj₁ x•y≈x | no  x≉y = sel₁ x•y≈x (λ x•y≈y → x≉y (trans (sym x•y≈x) x•y≈y))
  ... | inj₁ x•y≈x | yes x≈y = sel≈ x•y≈x (trans x•y≈x x≈y)
  ... | inj₂ x•y≈y | no  x≉y = sel₂ (λ x•y≈x → x≉y (trans (sym x•y≈x) x•y≈y)) x•y≈y
  ... | inj₂ x•y≈y | yes x≈y = sel≈ (trans x•y≈y (sym x≈y)) x•y≈y
