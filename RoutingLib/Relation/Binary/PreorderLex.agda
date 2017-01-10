

open import Data.Product using (_×_; _-×-_; _,_)
open import Data.Sum using (_⊎_; _-⊎-_; inj₁; inj₂)
open import Relation.Binary
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (flip)

open import RoutingLib.Relation.Binary

module RoutingLib.Relation.Binary.PreorderLex {a ℓ₁ ℓ₂} {A : Set a} (_≤₁_ : Rel A ℓ₁) (_≤₂_ : Rel A ℓ₂) where

  private
    _≰₁_ : Rel A ℓ₁
    x ≰₁ y = ¬ (x ≤₁ y) 
    
    _≰₂_ : Rel A ℓ₂
    x ≰₂ y = ¬ (x ≤₂ y)


  ×-Lex : Rel A _
  ×-Lex x y = x ≤₁ y × (y ≰₁ x ⊎ (y ≤₁ x × x ≤₂ y))

  ×-reflexive : ∀ {ℓ₃} {_≈_ : Rel A ℓ₃} → Symmetric _≈_ → _≈_ ⇒ _≤₁_ → _≈_ ⇒ _≤₂_ → _≈_ ⇒ ×-Lex
  ×-reflexive sym refl₁ refl₂ i≈j = refl₁ i≈j , inj₂ (refl₁ (sym i≈j) , refl₂ i≈j)

  ×-refl : Reflexive _≤₁_ → Reflexive _≤₂_ → Reflexive ×-Lex
  ×-refl refl₁ refl₂ = refl₁ , inj₂ (refl₁ , refl₂)

  ×-trans : Transitive _≤₁_ → Transitive _≤₂_ → Transitive ×-Lex
  ×-trans trans₁ trans₂ (x≤y , inj₁ _)            (y≤z , inj₁ z≰y)          = trans₁ x≤y y≤z , inj₁ (λ z≤x → z≰y (trans₁ z≤x x≤y))
  ×-trans trans₁ trans₂ (x≤y , inj₁ y≰x)          (y≤z , inj₂ (z≤y , _))    = trans₁ x≤y y≤z , inj₁ (λ z≤x → y≰x (trans₁ y≤z z≤x))
  ×-trans trans₁ trans₂ (x≤y , inj₂ (y≤x , _))    (y≤z , inj₁ z≰y)          = trans₁ x≤y y≤z , inj₁ (λ z≤x → z≰y (trans₁ z≤x x≤y))
  ×-trans trans₁ trans₂ (x≤y , inj₂ (y≤x , x≤₂y)) (y≤z , inj₂ (z≤y , y≤₂z)) = trans₁ x≤y y≤z , inj₂ (trans₁ z≤y y≤x , trans₂ x≤₂y y≤₂z)

  ×-antisym : ∀ {ℓ₃} {_≈_ : Rel A ℓ₃} → Antisymmetric _≈_ _≤₂_ → Antisymmetric _≈_ ×-Lex
  ×-antisym antisym (x≤y , inj₁ _)          (_   , inj₁ x≰y)        = contradiction x≤y x≰y
  ×-antisym antisym (_   , inj₁ y≰x)        (y≤x , inj₂ (_ , _))    = contradiction y≤x y≰x
  ×-antisym antisym (x≤y , inj₂ (_ , _))    (_   , inj₁ x≰y)        = contradiction x≤y x≰y
  ×-antisym antisym (_   , inj₂ (_ , x≤₂y)) (_   , inj₂ (_ , y≤₂x)) = antisym x≤₂y y≤₂x

  ×-decidable : Decidable _≤₁_ → Decidable _≤₂_ → Decidable ×-Lex
  ×-decidable _≤₁?_ _≤₂?_ x y with x ≤₁? y
  ... | no  x≰y = no (λ{(x≤y , _) → x≰y x≤y})
  ... | yes x≤y with y ≤₁? x
  ...   | no  y≰x = yes (x≤y , inj₁ y≰x)
  ...   | yes y≤x with x ≤₂? y
  ...     | yes x≤₂y = yes (x≤y , inj₂ (y≤x , x≤₂y))
  ...     | no  x≰₂y = no (λ{(_ , inj₁ y≰x) → y≰x y≤x; (_ , inj₂ (_ , x≤₂y)) → x≰₂y x≤₂y})

  ×-total : Total _≤₁_ → Decidable _≤₁_ → Total _≤₂_ → Total ×-Lex
  ×-total total₁ _≤?_ total₂ x y with total₁ x y
  ×-total total₁ _≤?_ total₂ x y | inj₁ x≤y with y ≤? x
  ... | no  y≰x = inj₁ (x≤y , inj₁ y≰x)
  ... | yes y≤x with total₂ x y
  ...   | inj₁ x≤₂y = inj₁ (x≤y , inj₂ (y≤x , x≤₂y))
  ...   | inj₂ y≤₂x = inj₂ (y≤x , inj₂ (x≤y , y≤₂x))
  ×-total total₁ _≤?_ total₂ x y | inj₂ y≤x with x ≤? y
  ... | no x≰y = inj₂ (y≤x , inj₁ x≰y)
  ... | yes x≤y with total₂ x y
  ...   | inj₁ x≤₂y = inj₁ (x≤y , inj₂ (y≤x , x≤₂y))
  ...   | inj₂ y≤₂x = inj₂ (y≤x , inj₂ (x≤y , y≤₂x))

  ×-resp : ∀ {ℓ₃} {_≈_ : Rel A ℓ₃} → Symmetric _≈_ → _≤₁_ Respects₂ _≈_ → _≤₂_ Respects₂ _≈_ → ×-Lex Respects₂ _≈_
  ×-resp {_} {_≈_} ≈-sym (r₁₁ , r₁₂) (r₂₁ , r₂₂) = resp₁ , resp₂
    where

    resp₁ : ∀ {x} → (×-Lex x) Respects _≈_
    resp₁ x≈y (z≤x , inj₁ x≰z) = r₁₁ x≈y z≤x , (inj₁ (λ y≤z → x≰z (r₁₂ (≈-sym x≈y) y≤z)))
    resp₁ x≈y (z≤x , inj₂ (x≤z , z≤₂x)) = r₁₁ x≈y z≤x , inj₂ (r₁₂ x≈y x≤z , r₂₁ x≈y z≤₂x)

    resp₂ : ∀ {y} → (flip ×-Lex y) Respects _≈_
    resp₂ y≈x (y≤z , inj₁ z≰y)          = r₁₂ y≈x y≤z , (inj₁ (λ z≤x → z≰y (r₁₁ (≈-sym y≈x) z≤x)))
    resp₂ y≈x (y≤z , inj₂ (z≤y , y≤₂z)) = r₁₂ y≈x y≤z , inj₂ (r₁₁ y≈x z≤y , r₂₂ y≈x y≤₂z)




  -- Records

  ×-isPreorder : ∀ {ℓ₃} {_≈_ : Rel A ℓ₃} → IsPreorder _≈_ _≤₁_ → IsPreorder _≈_ _≤₂_ → IsPreorder _≈_ ×-Lex
  ×-isPreorder pre₁ pre₂ = record { 
      isEquivalence = IsPreorder.isEquivalence pre₁; 
      reflexive = ×-reflexive (IsEquivalence.sym (IsPreorder.isEquivalence pre₁)) (IsPreorder.reflexive pre₁) (IsPreorder.reflexive pre₂) ; 
      trans = ×-trans (IsPreorder.trans pre₁) (IsPreorder.trans pre₂) 
    }

  ×-isPartialOrder : ∀ {ℓ₃} {_≈_ : Rel A ℓ₃} → IsPreorder _≈_ _≤₁_ → IsPartialOrder _≈_ _≤₂_ → IsPartialOrder _≈_ ×-Lex
  ×-isPartialOrder pre par = record { 
      isPreorder = ×-isPreorder pre (IsPartialOrder.isPreorder par) ; 
      antisym = ×-antisym (IsPartialOrder.antisym par) 
    }

  ×-isTotalOrder : ∀ {ℓ₃} {_≈_ : Rel A ℓ₃} → IsDecTotalPreorder _≈_ _≤₁_ → IsTotalOrder _≈_ _≤₂_ → IsTotalOrder _≈_ ×-Lex
  ×-isTotalOrder decTotPre tot = record { 
      isPartialOrder = ×-isPartialOrder (IsDecTotalPreorder.isPreorder decTotPre) (IsTotalOrder.isPartialOrder tot) ; 
      total = ×-total (IsDecTotalPreorder.total decTotPre) (IsDecTotalPreorder._≤?_ decTotPre) (IsTotalOrder.total tot) 
    }

  ×-isDecTotalOrder : ∀ {ℓ₃} {_≈_ : Rel A ℓ₃} → IsDecTotalPreorder _≈_ _≤₁_ → IsDecTotalOrder _≈_ _≤₂_ → IsDecTotalOrder _≈_ ×-Lex
  ×-isDecTotalOrder decTotPre decTot = record { 
      isTotalOrder = ×-isTotalOrder decTotPre (IsDecTotalOrder.isTotalOrder decTot) ; 
      _≟_ = IsDecTotalOrder._≟_ decTot; 
      _≤?_ = ×-decidable (IsDecTotalPreorder._≤?_ decTotPre) (IsDecTotalOrder._≤?_ decTot) 
    }
