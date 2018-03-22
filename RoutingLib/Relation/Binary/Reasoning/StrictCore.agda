open import Relation.Binary using (Rel; Transitive; _⇒_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)

module RoutingLib.Relation.Binary.Reasoning.StrictCore
  {a ℓ} {A : Set a}
  {_≤_ : Rel A ℓ} (≤-trans : Transitive _≤_) (≤-refl : _≡_ ⇒ _≤_) 
  {_<_ : Rel A ℓ} (<-trans : Transitive _<_)
  (<-≤-trans : ∀ {x y z} → x < y → y ≤ z → x < z)
  (≤-<-trans : ∀ {x y z} → x ≤ y → y < z → x < z)
  where

  data _≲_ (x y : A) : Set ℓ where
    strict    : x < y → x ≲ y
    nonstrict : x ≤ y → x ≲ y

  module _ {x y : A} where
  
    ⟦_⟧ : x ≲ y → Set ℓ
    ⟦ strict    _ ⟧ = x < y
    ⟦ nonstrict _ ⟧ = x ≤ y
    

  infix -1 begin_
  infixr 0 _≡⟨_⟩_ _<⟨_⟩_ _≤⟨_⟩_ _≡⟨⟩_
  infix  1 _∎ 

  begin_ : ∀ {x y} (p : x ≲ y) → ⟦ p ⟧
  begin strict    p = p
  begin nonstrict p = p
   
  _≡⟨_⟩_ : ∀ (x : A) {y z} → x ≡ y → y ≲ z → x ≲ z
  x ≡⟨ x=y ⟩ strict    y<z = strict    (case x=y of λ where refl → y<z)
  x ≡⟨ x=y ⟩ nonstrict y≤z = nonstrict (case x=y of λ where refl → y≤z)
    -- ^ Note: don't match on the proof here, we need to decide strict vs nonstrict for neutral proofs

  _≡⟨⟩_ : ∀ (x : A) {y} → x ≲ y → x ≲ y
  x ≡⟨⟩ x≲y = x≲y
  
  _<⟨_⟩_ : ∀ (x : A) {y z} → x < y → y ≲ z → x ≲ z
  x <⟨ x<y ⟩ strict    y<z = strict (<-trans x<y y<z)
  x <⟨ x<y ⟩ nonstrict y≤z = strict (<-≤-trans x<y y≤z)

  _≤⟨_⟩_ : ∀ (x : A) {y z} → x ≤ y → y ≲ z → x ≲ z
  x ≤⟨ x≤y ⟩ strict    y<z = strict    (≤-<-trans x≤y y<z)
  x ≤⟨ x≤y ⟩ nonstrict y≤z = nonstrict (≤-trans x≤y y≤z)

  _∎ : ∀ (x : A) → x ≲ x
  x ∎ = nonstrict (≤-refl refl)
