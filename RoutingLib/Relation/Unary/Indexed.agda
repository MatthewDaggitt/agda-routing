open import Data.Product
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)
open import Function using (id)
open import Level
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Unary as U using (Pred)
open import Relation.Binary hiding (Decidable)

module RoutingLib.Relation.Unary.Indexed {i} {I : Set i} where

IPred : ∀ {a} → (I → Set a) → (p : Level) → Set _
IPred A p = ∀ i → Pred (A i) p

--------------------------------------------------------------------------------
-- Special sets

U : ∀ {a} (Aᵢ : I → Set a) → IPred Aᵢ zero
U A x i = ⊤

--------------------------------------------------------------------------------
-- Membership

module _ {a} {Aᵢ : I → Set a} where

  _∈_ : ∀ {p} → (∀ i → Aᵢ i) → IPred Aᵢ p → Set _
  x ∈ P = ∀ i → x i U.∈ P i 

  _∉_ : ∀ {p} → (∀ i → Aᵢ i) → IPred Aᵢ p → Set _
  x ∉ P = ¬ (x ∈ P)

  _∈ᵢ_ : ∀ {p} {i} → Aᵢ i → IPred Aᵢ p → Set _
  x ∈ᵢ P = x U.∈ P _

  _∉ᵢ_ : ∀ {p} {i} → Aᵢ i → IPred Aᵢ p → Set _
  x ∉ᵢ P = ¬ (x ∈ᵢ P)
  
  member : ∀ {p} i → Aᵢ i → IPred Aᵢ p → Set _
  member i xᵢ P = P i xᵢ

  syntax member i xᵢ P = xᵢ ∈[ i ] P

--------------------------------------------------------------------------------
-- Relations

subset : ∀ {a} (Aᵢ : I → Set a) → ∀ {p} → Rel (IPred Aᵢ p) _
subset A P Q = ∀ {x} → x ∈ P → x ∈ Q

syntax subset A P Q = P ⊆[ A ] Q


_⊆ᵢ_ : ∀ {a p} {Aᵢ : I → Set a} → Rel (IPred Aᵢ p) _
P ⊆ᵢ Q = ∀ i → P i U.⊆ Q i

⊆-refl : ∀ {a p} (Aᵢ : I → Set a) → Reflexive (subset Aᵢ {p = p})
⊆-refl Aᵢ x i = x i

⊆-trans : ∀ {a p} (Aᵢ : I → Set a) → Transitive (subset Aᵢ {p = p})
⊆-trans Aᵢ x⊆y y⊆z i = y⊆z (x⊆y i)

--------------------------------------------------------------------------------
-- Properties

module _ {a} {Aᵢ : I → Set a} where

  IsSingleton : ∀ {p ℓ} → Rel (∀ i → Aᵢ i) ℓ → IPred Aᵢ p → (∀ i → Aᵢ i) → Set _
  IsSingleton _≈_ P x = (x ∈ P) × (∀ {y} → y ∈ P → y ≈ x)

  Decidable : ∀ {p} → IPred Aᵢ p → Set _
  Decidable P = ∀ x → Dec (x ∈ P)

  Decidableᵢ : ∀ {p} → IPred Aᵢ p → Set _
  Decidableᵢ P = ∀ {i} (x : Aᵢ i) → Dec (x ∈ᵢ P)
  
  Empty : ∀ {p} → IPred Aᵢ p → Set _
  Empty P = ∀ x → x ∉ P
  
--------------------------------------------------------------------------------
-- Construction

module _ {a} {Aᵢ : I → Set a} where

  ∁ : ∀ {ℓ} → IPred Aᵢ ℓ → IPred Aᵢ ℓ
  ∁ P i = λ x → x ∉ᵢ P

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
{-
  _[_] : ∀ {ℓ} → ((∀ i → Aᵢ i) → ∀ i → Aᵢ i) → IPred Aᵢ ℓ → IPred Aᵢ _
  (f [ P ∣ _≈_ ]) i = λ x → ∃ {!λ y → f y  x!}
-}
