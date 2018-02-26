open import Algebra.FunctionProperties using (Op₂)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel; _Preserves₂_⟶_⟶_; _Preserves_⟶_)

module RoutingLib.Algebra.FunctionProperties.Core {a} {A : Set a} where


  _⊎-Preservesˡ_ : Op₂ A → ∀ {p} → Pred A p → Set _
  _•_ ⊎-Preservesˡ P = ∀ {a} b → P a → P (a • b)

  _⊎-Preservesʳ_ : Op₂ A → ∀ {p} → Pred A p → Set _
  _•_ ⊎-Preservesʳ P = ∀ a {b} → P b → P (a • b)

  _⊎-Preserves_ : Op₂ A → ∀ {p} → Pred A p → Set _
  _•_ ⊎-Preserves P = ∀ a b → P a ⊎ P b → P (a • b)
  
  _×-Preserves_ : Op₂ A → ∀ {p} → Pred A p → Set _
  _•_ ×-Preserves P = ∀ {a b} → P a → P b → P (a • b)


  _Forces-×ˡ_ : Op₂ A → ∀ {p} → Pred A p → Set _
  _•_ Forces-×ˡ P = ∀ a b → P (a • b) → P a

  _Forces-×ʳ_ : Op₂ A → ∀ {p} → Pred A p → Set _
  _•_ Forces-×ʳ P = ∀ a b → P (a • b) → P b
  
  _Forces-×_ : Op₂ A → ∀ {p} → Pred A p → Set _
  _•_ Forces-× P = ∀ a b → P (a • b) → P a × P b

  _Forces-⊎_ : Op₂ A → ∀ {p} → Pred A p → Set _
  _•_ Forces-⊎ P = ∀ a b → P (a • b) → P a ⊎ P b



  ⊎pres⇒⊎presˡ : ∀ {_•_} {p} {P : Pred A p} →
                     _•_ ⊎-Preserves P → _•_ ⊎-Preservesˡ P
  ⊎pres⇒⊎presˡ pres b Pa = pres _ b (inj₁ Pa)

  ⊎pres⇒⊎presʳ : ∀ {_•_} {p} {P : Pred A p} →
                     _•_ ⊎-Preserves P → _•_ ⊎-Preservesʳ P
  ⊎pres⇒⊎presʳ pres a Pb = pres a _ (inj₂ Pb)

  forces×⇒forces×ˡ : ∀ {_•_} {p} {P : Pred A p} →
                     _•_ Forces-× P → _•_ Forces-×ˡ P
  forces×⇒forces×ˡ forces a b P = proj₁ (forces a b P)
  
  forces×⇒forces×ʳ : ∀ {_•_} {p} {P : Pred A p} →
                     _•_ Forces-× P → _•_ Forces-×ʳ P
  forces×⇒forces×ʳ forces a b P = proj₂ (forces a b P)
