open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable using (True; False; toWitness)
open import Function using (case_of_)
open import Level using (Level; _⊔_)

open import RoutingLib.Relation.Binary

module RoutingLib.Relation.Binary.Reasoning.StrictCore
  {a ℓ₁ ℓ₂ ℓ₃} (OP : OrderingPair a ℓ₁ ℓ₂ ℓ₃)
  where

open OrderingPair OP renaming (Carrier to A)

------------------------------------------------------------------------
-- This additonal relation "hides" whether the current relation is
-- strict or non strict or an equality.

data _≲_ (x y : A) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  strict    : x < y → x ≲ y
  nonstrict : x ≤ y → x ≲ y
  eq        : x ≈ y → x ≲ y
  
levelOf : ∀ {x y} → x ≲ y → Level
levelOf (eq x≈y)        = ℓ₁
levelOf (nonstrict x≤y) = ℓ₂
levelOf (strict x<y)    = ℓ₃

------------------------------------------------------------------------
-- This type is used to test if a strict relation has been proved and
-- if so then extract that relation.

module _ {x y : A} where

  ⟦_⟧ : (r : x ≲ y) → Set (levelOf r)
  ⟦ eq        x≈y ⟧ = x ≈ y
  ⟦ nonstrict x≤y ⟧ = x ≤ y
  ⟦ strict    x<y ⟧ = x < y

------------------------------------------------------------------------
-- Reasoning combinators

infix  3 _∎
infixr 2 _<⟨_⟩_ _≤⟨_⟩_ _≈⟨_⟩_ _≡⟨_⟩_ _≡⟨⟩_
infix  1 begin_

begin_ : ∀ {x y} → (p : x ≲ y) → ⟦ p ⟧
begin strict    p = p
begin nonstrict p = p
begin eq        p = p

_<⟨_⟩_ : ∀ (x : A) {y z} → x < y → y ≲ z → x ≲ z
x <⟨ x<y ⟩ eq        y≈z = strict (<-respʳ-≈ y≈z x<y)
x <⟨ x<y ⟩ strict    y<z = strict (SPO.trans x<y y<z)
x <⟨ x<y ⟩ nonstrict y≤z = strict (<-≤-trans x<y y≤z)

_≤⟨_⟩_ : ∀ (x : A) {y z} → x ≤ y → y ≲ z → x ≲ z
x ≤⟨ x≤y ⟩ eq        y≈z = nonstrict (PO.≤-respʳ-≈ y≈z x≤y)
x ≤⟨ x≤y ⟩ strict    y<z = strict    (≤-<-trans x≤y y<z)
x ≤⟨ x≤y ⟩ nonstrict y≤z = nonstrict (PO.trans x≤y y≤z)

_≈⟨_⟩_ : ∀ (x : A) {y z} → x ≈ y → y ≲ z → x ≲ z
x ≈⟨ x≈y ⟩ eq        y≈z = eq (Eq.trans x≈y y≈z)
x ≈⟨ x≈y ⟩ strict    y<z = strict    (<-respˡ-≈ (Eq.sym x≈y) y<z)
x ≈⟨ x≈y ⟩ nonstrict y≤z = nonstrict (PO.≤-respˡ-≈ (Eq.sym x≈y) y≤z)

-- Note: the proof of propostional equality is not matched on in the
-- combinator below as we need to decide strict vs nonstrict for
-- neutral proofs

_≡⟨_⟩_ : ∀ (x : A) {y z} → x ≡ y → y ≲ z → x ≲ z
x ≡⟨ x≡y ⟩ eq        y≈z = eq        (case x≡y of λ where refl → y≈z)
x ≡⟨ x≡y ⟩ strict    y<z = strict    (case x≡y of λ where refl → y<z)
x ≡⟨ x≡y ⟩ nonstrict y≤z = nonstrict (case x≡y of λ where refl → y≤z)

_≡⟨⟩_ : ∀ (x : A) {y} → x ≲ y → x ≲ y
x ≡⟨⟩ x≲y = x≲y

_∎ : ∀ (x : A) → x ≲ x
x ∎ = nonstrict PO.refl




{-
-- Tests
postulate
  u v w x y z b c : A
  u≈v : u ≈ v
  v≡w : v ≡ w
  w<x : w < x
  x≤y : x ≤ y
  y<z : y < z
  z≡b : z ≡ b
  b≈c : b ≈ c

u≤c : u ≤ c
u≤c = begin
  u ≈⟨ u≈v ⟩
  v ≡⟨ v≡w ⟩
  w <⟨ w<x ⟩
  x ≤⟨ x≤y ⟩
  y <⟨ y<z ⟩
  z ≡⟨ z≡b ⟩
  b ≈⟨ b≈c ⟩
  c ∎

u<c : u < c
u<c = begin-strict
  u ≈⟨ u≈v ⟩
  v ≡⟨ v≡w ⟩
  w <⟨ w<x ⟩
  x ≤⟨ x≤y ⟩
  y <⟨ y<z ⟩
  z ≡⟨ z≡b ⟩
  b ≈⟨ b≈c ⟩
  c ∎
-}
