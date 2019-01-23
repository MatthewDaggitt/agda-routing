open import Data.Product
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)
open import Function using (id)
open import Level
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Unary using (Pred; _∈_; _⊆_)
open import Relation.Binary hiding (Decidable)

module RoutingLib.Relation.Unary.Indexed {i} {I : Set i} where

IPred : ∀ {a} → (I → Set a) → (p : Level) → Set _
IPred A p = ∀ i → Pred (A i) p

--------------------------------------------------------------------------------
-- Special sets

Uᵢ : ∀ {a} {Aᵢ : I → Set a} → IPred Aᵢ zero
Uᵢ x i = ⊤

--------------------------------------------------------------------------------
-- Membership

module _ {a} {Aᵢ : I → Set a} where

  _∈ᵢ_ : ∀ {p} → (∀ i → Aᵢ i) → IPred Aᵢ p → Set _
  x ∈ᵢ P = ∀ i → x i ∈ P i

  _∉ᵢ_ : ∀ {p} → (∀ i → Aᵢ i) → IPred Aᵢ p → Set _
  x ∉ᵢ P = ¬ (x ∈ᵢ P)

{-
  _∈ᵢ_ : ∀ {p} {i} → Aᵢ i → IPred Aᵢ p → Set _
  x ∈ᵢ P = x U.∈ P _

  _∉ᵢ_ : ∀ {p} {i} → Aᵢ i → IPred Aᵢ p → Set _
  x ∉ᵢ P = ¬ (x ∈ᵢ P)

  member : ∀ {p} i → Aᵢ i → IPred Aᵢ p → Set _
  member i xᵢ P = P i xᵢ

  syntax member i xᵢ P = xᵢ ∈[ i ] P
-}

--------------------------------------------------------------------------------
-- Relations

subset : ∀ {a} (Aᵢ : I → Set a) → ∀ {p} → Rel (IPred Aᵢ p) _
subset A P Q = ∀ {x} → x ∈ᵢ P → x ∈ᵢ Q

syntax subset A P Q = P ⊆ᵢ[ A ] Q


_⊆ᵢ_ : ∀ {a p q} {Aᵢ : I → Set a} → REL (IPred Aᵢ p) (IPred Aᵢ q) _
P ⊆ᵢ Q = ∀ {i} → P i ⊆ Q i

⊆-refl : ∀ {a p} (Aᵢ : I → Set a) → Reflexive (subset Aᵢ {p = p})
⊆-refl Aᵢ x i = x i

⊆-trans : ∀ {a p} (Aᵢ : I → Set a) → Transitive (subset Aᵢ {p = p})
⊆-trans Aᵢ x⊆y y⊆z i = y⊆z (x⊆y i)

_≋ᵢ_ : ∀ {a p q} {Aᵢ : I → Set a} → REL (IPred Aᵢ p) (IPred Aᵢ q) _
p ≋ᵢ q = (p ⊆ᵢ q) × (q ⊆ᵢ p)

--------------------------------------------------------------------------------
-- Properties

module _ {a} {Aᵢ : I → Set a} where

  Universalᵢ : ∀ {ℓ} → Pred (IPred Aᵢ ℓ) (i ⊔ a ⊔ ℓ)
  Universalᵢ P = ∀ {i} x → x ∈ P i

  IsSingleton : ∀ {p ℓ} → Rel (∀ i → Aᵢ i) ℓ → IPred Aᵢ p → (∀ i → Aᵢ i) → Set _
  IsSingleton _≈_ P x = (x ∈ᵢ P) × (∀ {y} → y ∈ᵢ P → y ≈ x)

  Decidableᵢ : ∀ {p} → IPred Aᵢ p → Set _
  Decidableᵢ P = ∀ x → Dec (x ∈ᵢ P)

  Empty : ∀ {p} → IPred Aᵢ p → Set _
  Empty P = ∀ x → x ∉ᵢ P

--------------------------------------------------------------------------------
-- Construction

module _ {a} {Aᵢ : I → Set a} where

{-
  ∁ : ∀ {ℓ} → IPred Aᵢ ℓ → IPred Aᵢ ℓ
  ∁ P i = λ x → x ∉ᵢ P i

  infixr 6 _∪_
  _∪_ : ∀ {ℓ₁ ℓ₂} → IPred Aᵢ ℓ₁ → IPred Aᵢ ℓ₂ → IPred Aᵢ _
  (P ∪ Q) i = λ x → x ∈ᵢ P ⊎ x ∈ᵢ Q

  infixr 7 _∩_
  _∩_ : ∀ {ℓ₁ ℓ₂} → IPred Aᵢ ℓ₁ → IPred Aᵢ ℓ₂ → IPred Aᵢ _
  (P ∩ Q) i = λ x → x ∈ᵢ P × x ∈ᵢ Q

  ⋃ : ∀ {ℓ j} (J : Set j) → (J → IPred Aᵢ ℓ) → IPred Aᵢ _
  ⋃ J P i = λ x → Σ[ j ∈ J ] P j i x

  _/_ : ∀ {ℓ₁ ℓ₂} → IPred Aᵢ ℓ₁ → IPred Aᵢ ℓ₂ → IPred Aᵢ _
  (P / Q) i = λ x → x ∈ᵢ P × x ∉ᵢ Q


  ⋃-⊆⁺ : ∀ {ℓ j} {J : Set j} {P : J → IPred Aᵢ ℓ} {Q : J → IPred Aᵢ ℓ} →
         (∀ j → P j ⊆ᵢ Q j) → ⋃ J P ⊆[ Aᵢ ] ⋃ J Q
  ⋃-⊆⁺ Pⱼ⊆Qⱼ x∈⋃P i = map id (λ {j} xᵢ∈Pⱼᵢ → Pⱼ⊆Qⱼ j i xᵢ∈Pⱼᵢ) (x∈⋃P i)

  _[_] : ∀ {ℓ} → ((∀ i → Aᵢ i) → ∀ i → Aᵢ i) → IPred Aᵢ ℓ → IPred Aᵢ _
  (f [ P ∣ _≈_ ]) i = λ x → ∃ {!λ y → f y  x!}
-}
