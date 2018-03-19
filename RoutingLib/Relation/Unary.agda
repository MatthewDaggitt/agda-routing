
open import Data.Product using (_×_; _,_; swap)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Unary
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Nullary.Sum using (_⊎-dec_)

open import RoutingLib.Relation.Nullary.Product using (~-dec)

module RoutingLib.Relation.Unary where

  -----------------------
  -- To push to stdlib --
  -----------------------

  _Preserves_ : ∀ {a p} {A : Set a} → (A → A) → Pred A p → Set _
  f Preserves P = ∀ {a} → P a → P (f a)

  _Forces_ : ∀ {a p} {A : Set a} → (A → A) → Pred A p → Set _
  f Forces P = ∀ {a} → P (f a) → P a

  module _ {a} {A : Set a} where

    _∪?_ : ∀ {ℓ₁ ℓ₂} {P : Pred A ℓ₁} {Q : Pred A ℓ₂} →
           Decidable P → Decidable Q → Decidable (P ∪ Q)
    _∪?_ P? Q? x = (P? x) ⊎-dec (Q? x)
    
    _∩?_ : ∀ {ℓ₁ ℓ₂} {P : Pred A ℓ₁} {Q : Pred A ℓ₂} →
           Decidable P → Decidable Q → Decidable (P ∩ Q)
    _∩?_ P? Q? x = (P? x) ×-dec (Q? x)
    
    
  module _ {a b} {A : Set a} {B : Set b} where
    
    _×?_ : ∀ {ℓ₁ ℓ₂} {P : Pred A ℓ₁} {Q : Pred B ℓ₂} →
           Decidable P → Decidable Q → Decidable (P ⟨×⟩ Q)
    _×?_ P? Q? (a , b) = (P? a) ×-dec (Q? b)

    _⊙?_ : ∀ {ℓ₁ ℓ₂} {P : Pred A ℓ₁} {Q : Pred B ℓ₂} → 
           Decidable P → Decidable Q → Decidable (P ⟨⊙⟩ Q)
    _⊙?_ P? Q? (a , b) = (P? a) ⊎-dec (Q? b)

    _⊎?_ : ∀ {ℓ} {P : Pred A ℓ} {Q : Pred B ℓ} → 
           Decidable P → Decidable Q → Decidable (P ⟨⊎⟩ Q)
    _⊎?_ P? Q? (inj₁ a) = P? a
    _⊎?_ P? Q? (inj₂ b) = Q? b

    _~? : ∀ {ℓ} {P : Pred (A × B) ℓ} →
          Decidable P → Decidable (P ~)
    _~? P? = P? ∘ swap
