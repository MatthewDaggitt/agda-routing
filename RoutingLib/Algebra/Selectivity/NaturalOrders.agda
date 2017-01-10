open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary
open import Algebra.FunctionProperties.Core using (Op₂)

open import RoutingLib.Algebra.FunctionProperties using (_Preserves_)
open import RoutingLib.Relation.Binary.RespectedBy using (_RespectedBy_; Respects₂⇨RespectedBy)

module RoutingLib.Algebra.Selectivity.NaturalOrders 
  {a ℓ} (S : Setoid a ℓ) (_•_ : Op₂ (Setoid.Carrier S)) (pres : _•_ Preserves (Setoid._≈_ S))
  where

  open Setoid S renaming (Carrier to A)
  open import Algebra.FunctionProperties _≈_ using (Commutative; Associative; Idempotent)
  open import RoutingLib.Algebra.FunctionProperties _≈_ using (Selective)
  open import RoutingLib.Algebra.Selectivity.Properties _≈_ _•_ using () renaming (idem to sel⇨idem)

  ------------------------
  -- Left natural order --
  ------------------------

  infix 4 _≤ₗ_

  _≤ₗ_ : Rel A ℓ
  x ≤ₗ y = (x • y) ≈ x

  -- Properties

  ≤ₗ-reflexive : Idempotent _•_ → _≈_ ⇒ _≤ₗ_ 
  ≤ₗ-reflexive idem {x} x≈y = trans (sym (pres refl x≈y)) (idem x)

  ≤ₗ-refl : Idempotent _•_ → Reflexive _≤ₗ_ 
  ≤ₗ-refl idem {x} = idem x

  ≤ₗ-antisym : Commutative _•_ → Antisymmetric _≈_ _≤ₗ_
  ≤ₗ-antisym comm {x} {y} x≤y y≤x = trans (trans (sym x≤y) (comm x y)) y≤x

  ≤ₗ-total : Selective _•_ → Commutative _•_ → Total _≤ₗ_
  ≤ₗ-total sel comm x y with sel x y
  ... | inj₁ x•y≈x = inj₁ x•y≈x
  ... | inj₂ x•y≈y = inj₂ (trans (comm y x ) x•y≈y)

  ≤ₗ-trans : Associative _•_ → Transitive _≤ₗ_
  ≤ₗ-trans assoc {x} {y} {z} x≤y y≤z = trans (trans (trans (pres (sym x≤y) refl) (assoc x y z)) (pres refl y≤z)) x≤y

  ≤ₗ-resp₁ : ∀ {x} → (x •_) Preserves _≈_ ⟶ _≈_ → (x ≤ₗ_) Respects _≈_
  ≤ₗ-resp₁ pres x≈y x≤z = trans (pres (sym x≈y)) x≤z

  ≤ₗ-resp₂ : ∀ {y} → (_• y) Preserves _≈_ ⟶ _≈_ → (_≤ₗ y) Respects _≈_
  ≤ₗ-resp₂ pres z≈x z≤y = trans (trans (pres (sym z≈x)) z≤y) z≈x

  ≤ₗ-resp₂-≈ : _≤ₗ_ Respects₂ _≈_
  ≤ₗ-resp₂-≈ = (≤ₗ-resp₁ presₗ) , (≤ₗ-resp₂ presᵣ)
    where

    presₗ : ∀ {x} → (x •_) Preserves _≈_ ⟶ _≈_
    presₗ i≈j = pres refl i≈j

    presᵣ : ∀ {y} → (_• y) Preserves _≈_ ⟶ _≈_
    presᵣ i≈j = pres i≈j refl

  ≤ₗ-resp-≈ : _≤ₗ_ RespectedBy _≈_
  ≤ₗ-resp-≈ = Respects₂⇨RespectedBy ≤ₗ-resp₂-≈

  ≤ₗ-isPreorder : Associative _•_ → Idempotent _•_ → IsPreorder _≈_ _≤ₗ_
  ≤ₗ-isPreorder assoc idem = record {
      isEquivalence = isEquivalence;
      reflexive = ≤ₗ-reflexive idem;
      trans = ≤ₗ-trans assoc
    }

  ≤ₗ-preorder : Associative _•_ → Idempotent _•_ → Preorder a ℓ ℓ
  ≤ₗ-preorder assoc idem = record {
      Carrier = A;
      _≈_ = _≈_;
      _∼_ = _≤ₗ_;
      isPreorder = ≤ₗ-isPreorder assoc idem
    }



  -------------------------
  -- Right natural order --
  -------------------------

  infix 4 _≤ᵣ_

  _≤ᵣ_ : Rel A ℓ
  x ≤ᵣ y = (y • x) ≈ x

  -- Properties 

  ≤ᵣ-reflexive : Idempotent _•_ → _≈_ ⇒ _≤ᵣ_ 
  ≤ᵣ-reflexive idem {x} x≈y = trans (pres (sym x≈y) refl) (idem x)

  ≤ᵣ-refl : Idempotent _•_ → Reflexive _≤ᵣ_ 
  ≤ᵣ-refl idem {x} = idem x

  ≤ᵣ-antisym : Commutative _•_ → Antisymmetric _≈_ _≤ᵣ_
  ≤ᵣ-antisym comm {x} {y} x≤y y≤x = trans (trans (sym x≤y) (comm y x)) y≤x

  ≤ᵣ-total : Selective _•_ → Commutative _•_ → Total _≤ᵣ_
  ≤ᵣ-total sel comm x y with sel x y
  ... | inj₁ x•y≈x = inj₁ (trans (comm y x) x•y≈x)
  ... | inj₂ x•y≈y = inj₂ x•y≈y

  ≤ᵣ-trans : Associative _•_ → Transitive _≤ᵣ_
  ≤ᵣ-trans assoc {x} {y} {z} x≤y y≤z = trans (trans (trans (pres refl (sym x≤y)) (sym (assoc z y x))) (pres y≤z refl)) x≤y

  ≤ᵣ-respᵣ-≈ : ∀ {x} → (x ≤ᵣ_) Respects _≈_
  ≤ᵣ-respᵣ-≈ x≈y x≤z = trans (pres (sym x≈y) refl) x≤z

  ≤ᵣ-respₗ-≈ : ∀ {x} → (_≤ᵣ x) Respects _≈_
  ≤ᵣ-respₗ-≈ z≈x z≤y = trans (trans (pres refl (sym z≈x)) z≤y) z≈x

  ≤ᵣ-resp₂-≈ : _≤ᵣ_ Respects₂ _≈_
  ≤ᵣ-resp₂-≈ = ≤ᵣ-respᵣ-≈ , ≤ᵣ-respₗ-≈

  ≤ᵣ-resp-≈ : _≤ᵣ_ RespectedBy _≈_
  ≤ᵣ-resp-≈ = Respects₂⇨RespectedBy ≤ᵣ-resp₂-≈

  ≤ᵣ-absₗ : Associative _•_ → Idempotent _•_ → ∀ x y → x • y ≤ᵣ x
  ≤ᵣ-absₗ assoc idem x y = trans (sym (assoc x x y)) (pres (idem x) refl)

  ≤ᵣ-absᵣ : Commutative _•_ → Associative _•_ → Idempotent _•_ → ∀ x y → y • x ≤ᵣ x
  ≤ᵣ-absᵣ comm assoc idem x y = trans (trans (trans (sym (assoc x y x)) (pres (comm x y) refl)) (assoc y x x)) (pres refl (idem x))

  ≤ᵣ-dec : Decidable _≈_ → Decidable _≤ᵣ_
  ≤ᵣ-dec dec x y = dec (y • x) x

  ≤ᵣ-isPreorder : Associative _•_ → Idempotent _•_ → IsPreorder _≈_ _≤ᵣ_
  ≤ᵣ-isPreorder assoc idem = record {
      isEquivalence = isEquivalence;
      reflexive = ≤ᵣ-reflexive idem;
      trans = ≤ᵣ-trans assoc
    }

  ≤ᵣ-preorder : Associative _•_ → Idempotent _•_ → Preorder a ℓ ℓ
  ≤ᵣ-preorder assoc idem = record {
      Carrier = A;
      _≈_ = _≈_;
      _∼_ = _≤ᵣ_;
      isPreorder = ≤ᵣ-isPreorder assoc idem
    }

  ≤ᵣ-isPartialOrder : Commutative _•_ → Associative _•_ → Idempotent _•_ → IsPartialOrder _≈_ _≤ᵣ_
  ≤ᵣ-isPartialOrder comm assoc idem = record { 
      isPreorder = ≤ᵣ-isPreorder assoc idem; 
      antisym = ≤ᵣ-antisym comm 
    }

  ≤ᵣ-poset : Commutative _•_ → Associative _•_ → Idempotent _•_ →  Poset a ℓ ℓ
  ≤ᵣ-poset comm assoc idem = record { 
      Carrier = A ; 
      _≈_ = _≈_ ; 
      _≤_ = _≤ᵣ_ ; 
      isPartialOrder = ≤ᵣ-isPartialOrder comm assoc idem
    }

  ≤ᵣ-isDecPartialOrder : Decidable _≈_ → Commutative _•_ → Associative _•_ → Idempotent _•_ → IsDecPartialOrder _≈_ _≤ᵣ_
  ≤ᵣ-isDecPartialOrder dec comm assoc idem = record { 
      isPartialOrder = ≤ᵣ-isPartialOrder comm assoc idem ; 
      _≟_ = dec; 
      _≤?_ = ≤ᵣ-dec dec 
    }

  ≤ᵣ-decPoset : Decidable _≈_ → Commutative _•_ → Associative _•_ → Idempotent _•_ → DecPoset a ℓ ℓ
  ≤ᵣ-decPoset dec comm assoc idem = record { 
      Carrier = A ; 
      _≈_ = _≈_ ; 
      _≤_ = _≤ᵣ_ ; 
      isDecPartialOrder = ≤ᵣ-isDecPartialOrder dec comm assoc idem
    }

  ≤ᵣ-isTotalOrder : Commutative _•_ → Associative _•_ → Selective _•_ → IsTotalOrder _≈_ _≤ᵣ_
  ≤ᵣ-isTotalOrder comm assoc sel  = record { 
      isPartialOrder = ≤ᵣ-isPartialOrder comm assoc (sel⇨idem sel) ; 
      total = ≤ᵣ-total sel comm 
    }

  ≤ᵣ-totalOrder : Commutative _•_ → Associative _•_ → Selective _•_ → TotalOrder a ℓ ℓ
  ≤ᵣ-totalOrder comm assoc sel = record { 
      Carrier = A ; 
      _≈_ = _≈_ ; 
      _≤_ = _≤ᵣ_ ; 
      isTotalOrder = ≤ᵣ-isTotalOrder comm assoc sel 
    }


  -----------------------------------
  -- Relationship between ≤ₗ and ≤ᵣ --
  -----------------------------------

  ≤ᵣ⇨≤ₗ : Commutative _•_ → ∀ {x y} → x ≤ᵣ y → x ≤ₗ y
  ≤ᵣ⇨≤ₗ comm {x} {y} y⊕x≈x = trans (comm x y) y⊕x≈x
  
  ≤ₗ⇨≤ᵣ : Commutative _•_ → ∀ {x y} → x ≤ₗ y → x ≤ᵣ y
  ≤ₗ⇨≤ᵣ comm {x} {y} x⊕y≈x = trans (comm y x) x⊕y≈x
