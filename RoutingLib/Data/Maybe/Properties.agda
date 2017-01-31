
open import Data.Maybe using (Maybe; nothing; just; Eq; drop-just)
open import Relation.Binary using (Rel; Reflexive; Symmetric; Transitive; Decidable; IsEquivalence; IsDecEquivalence; Setoid; DecSetoid; _⇒_)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)
open import Relation.Nullary using (¬_; yes; no)
open import Function using (_∘_)

module RoutingLib.Data.Maybe.Properties where

  just-injective : ∀ {a} {A : Set a} {x y : A} → (_≡_ {A = Maybe A}) (just x) (just y) → x ≡ y
  just-injective ≡-refl = ≡-refl



  ----------------------
  -- Pushed to stdlib --
  ----------------------

  reflexive : ∀ {a ℓ} {A : Set a} {_≈_ : Rel A ℓ} →
              Reflexive _≈_ → _≡_ ⇒ (Eq _≈_)
  reflexive _    {i = nothing} ≡-refl = nothing
  reflexive refl {i = just v} ≡-refl = just refl

  refl : ∀ {a ℓ} {A : Set a} {_≈_ : Rel A ℓ} →
       Reflexive _≈_ → Reflexive (Eq _≈_)
  refl refl {just x}  = just refl
  refl _    {nothing} = nothing

  sym :  ∀ {a ℓ} {A : Set a} {_≈_ : Rel A ℓ} →
         Symmetric _≈_ → Symmetric (Eq _≈_)
  sym sym (just x≈y) = just (sym x≈y)
  sym sym nothing    = nothing

  trans : ∀ {a ℓ} {A : Set a} {_≈_ : Rel A ℓ} →
        Transitive _≈_ → Transitive (Eq _≈_)
  trans trans (just x≈y) (just y≈z) = just (trans x≈y y≈z)
  trans trans nothing    nothing    = nothing

  dec : ∀ {a ℓ} {A : Set a} {_≈_ : Rel A ℓ} →
        Decidable _≈_ → Decidable (Eq _≈_)
  dec dec (just x) (just y)  with dec x y
  ...  | yes x≈y = yes (just x≈y)
  ...  | no  x≉y = no (x≉y ∘ drop-just)
  dec dec (just x) nothing = no λ()
  dec dec nothing (just y)  = no λ()
  dec dec nothing nothing = yes nothing

  isEquivalence : ∀ {a ℓ} {A : Set a} {_≈_ : Rel A ℓ}
                  → IsEquivalence _≈_ → IsEquivalence (Eq _≈_)
  isEquivalence isEq = record
    { refl  = refl (IsEquivalence.refl isEq)
    ; sym   = sym (IsEquivalence.sym isEq)
    ; trans = trans (IsEquivalence.trans isEq)
    }

  isDecEquivalence : ∀ {a ℓ} {A : Set a} {_≈_ : Rel A ℓ}
                   → IsDecEquivalence _≈_ → IsDecEquivalence (Eq _≈_)
  isDecEquivalence isDecEq = record
    { isEquivalence = isEquivalence
                        (IsDecEquivalence.isEquivalence isDecEq)
    ; _≟_           = dec (IsDecEquivalence._≟_ isDecEq)
    }
