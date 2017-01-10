open import Algebra.FunctionProperties using (Op₂)
open import Data.Product using (_×_; proj₁)
open import Data.Sum using (_⊎_; inj₁)
open import Relation.Binary using (Rel; _Preserves₂_⟶_⟶_; _Preserves_⟶_)

module RoutingLib.Algebra.FunctionProperties.Core where

  _Preserves_ : ∀ {a ℓ} {A : Set a} → Op₂ A → Rel A ℓ → Set _
  _•_ Preserves _≈_ = _•_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_

  _Preservesₗ_ : ∀ {a b ℓ} {A : Set a} {B : Set b} → (B → A → A) → Rel A ℓ → Set _
  _▷_ Preservesₗ _≈_  = ∀ b {x y} → x ≈ y → (b ▷ x) ≈ (b ▷ y)




  _×-Preserves_ : ∀ {a} {A : Set a} → Op₂ A → ∀ {p} → (A → Set p) → Set _
  _•_ ×-Preserves P = ∀ {a b} → P a → P b → P (a • b)

  _⊎-Preserves_ : ∀ {a} {A : Set a} → Op₂ A → ∀ {p} → (A → Set p) → Set _
  _•_ ⊎-Preserves P = ∀ {a b} → P a ⊎ P b → P (a • b)

  _Forces-×_ : ∀ {a} {A : Set a} → Op₂ A → ∀ {p} → (A → Set p) → Set _
  _•_ Forces-× P = ∀ {a b} → P (a • b) → P a × P b

  _Forces-⊎_ : ∀ {a} {A : Set a} → Op₂ A → ∀ {p} → (A → Set p) → Set _
  _•_ Forces-⊎ P = ∀ {a b} → P (a • b) → P a ⊎ P b
  


  ⊎Preserves⇨×Preserves : ∀ {a} {A : Set a} (_•_ : Op₂ A) {p} (P : A → Set p) → _•_ ⊎-Preserves P → _•_ ×-Preserves P
  ⊎Preserves⇨×Preserves _ _ ⊎pres pa _ = ⊎pres (inj₁ pa)

  Forces×⇨Forces⊎ : ∀ {a} {A : Set a} (_•_ : Op₂ A) {p} (P : A → Set p) → _•_ Forces-× P → _•_ Forces-⊎ P
  Forces×⇨Forces⊎ _ _ forces× pa•b = inj₁ (proj₁ (forces× pa•b))
