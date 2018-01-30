open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary
open import Relation.Nullary using (¬_)
open import Algebra.FunctionProperties using (Congruent₂; Op₂)
open import Algebra.Structures

open import RoutingLib.Relation.Binary.RespectedBy using (_RespectedBy_; Respects₂⇨RespectedBy)

module RoutingLib.Algebra.Selectivity.LeftNaturalOrder
  {a ℓ} (S : Setoid a ℓ) (_•_ : Op₂ (Setoid.Carrier S))
  where

  open Setoid S renaming (Carrier to A)
  open import Algebra.FunctionProperties _≈_
    using (Commutative; Associative; Idempotent; Selective)
  open import RoutingLib.Algebra.Selectivity.Properties _≈_ _•_
    using () renaming (idem to sel⇨idem)

  ------------------------
  -- Left natural order --
  ------------------------

  infix 4 _≤_ _≰_

  _≤_ : Rel A ℓ
  x ≤ y = (x • y) ≈ x

  _≰_ : Rel A ℓ
  x ≰ y = ¬ (x ≤ y)

  _<_ : Rel A ℓ
  x < y = x ≤ y × ¬ (x ≈ y)

  _≮_ : Rel A ℓ
  x ≮ y = ¬ (x < y)


  -- Properties

  ≤-reflexive : Idempotent _•_ → _≈_ ⇒ _≤_
  ≤-reflexive idem {x} x≈y = {!!} --trans (sym (pres refl x≈y)) (idem x)

  ≤-refl : Idempotent _•_ → Reflexive _≤_
  ≤-refl idem {x} = idem x

  ≤-antisym : Commutative _•_ → Antisymmetric _≈_ _≤_
  ≤-antisym comm {x} {y} x≤y y≤x = trans (trans (sym x≤y) (comm x y)) y≤x

  ≤-total : Selective _•_ → Commutative _•_ → Total _≤_
  ≤-total sel comm x y with sel x y
  ... | inj₁ x•y≈x = inj₁ x•y≈x
  ... | inj₂ x•y≈y = inj₂ (trans (comm y x ) x•y≈y)

  ≤-trans : Associative _•_ → Transitive _≤_
  ≤-trans assoc {x} {y} {z} x≤y y≤z = {!!}
  {-
    trans (trans (trans (pres (sym x≤y) refl) (assoc x y z)) (pres refl y≤z)) x≤y
  -}
  
  ≤-resp₁ : ∀ {x} → (x •_) Preserves _≈_ ⟶ _≈_ → (x ≤_) Respects _≈_
  ≤-resp₁ pres x≈y x≤z = trans (pres (sym x≈y)) x≤z

  ≤-resp₂ : ∀ {y} → (_• y) Preserves _≈_ ⟶ _≈_ → (_≤ y) Respects _≈_
  ≤-resp₂ pres z≈x z≤y = trans (trans (pres (sym z≈x)) z≤y) z≈x

  ≤-resp₂-≈ : _≤_ Respects₂ _≈_
  ≤-resp₂-≈ = (≤-resp₁ presₗ) , (≤-resp₂ presᵣ)
    where

    presₗ : ∀ {x} → (x •_) Preserves _≈_ ⟶ _≈_
    presₗ i≈j = {!!} --pres refl i≈j

    presᵣ : ∀ {y} → (_• y) Preserves _≈_ ⟶ _≈_
    presᵣ i≈j = {!!} --pres i≈j refl

  ≤-resp-≈ : _≤_ RespectedBy _≈_
  ≤-resp-≈ = Respects₂⇨RespectedBy ≤-resp₂-≈

  ≤-isPreorder : Associative _•_ → Idempotent _•_ → IsPreorder _≈_ _≤_
  ≤-isPreorder assoc idem = record {
      isEquivalence = isEquivalence;
      reflexive = ≤-reflexive idem;
      trans = ≤-trans assoc
    }

  ≤-preorder : Associative _•_ → Idempotent _•_ → Preorder a ℓ ℓ
  ≤-preorder assoc idem = record
    { Carrier    = A
    ;  _≈_       = _≈_
    ; _∼_        = _≤_
    ; isPreorder = ≤-isPreorder assoc idem
    }

{-
  ≤ᵣ⇨≤ₗ : Commutative _•_ → ∀ {x y} → x ≤ᵣ y → x ≤ₗ y
  ≤ᵣ⇨≤ₗ comm {x} {y} y⊕x≈x = trans (comm x y) y⊕x≈x

  ≤ₗ⇨≤ᵣ : Commutative _•_ → ∀ {x y} → x ≤ₗ y → x ≤ᵣ y
  ≤ₗ⇨≤ᵣ comm {x} {y} x⊕y≈x = trans (comm y x) x⊕y≈x
-}
