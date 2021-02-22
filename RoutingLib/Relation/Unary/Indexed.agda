open import Data.Product
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)
open import Function using (id; _∘_)
open import Level
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Unary using (Pred; _∈_; _⊆_)
open import Relation.Binary hiding (Decidable)

module RoutingLib.Relation.Unary.Indexed {i} {I : Set i} where

private
  variable
    a p q ℓ ℓ₁ ℓ₂ : Level
    Aᵢ : I → Set a

--------------------------------------------------------------------------------
-- Definition

IPred : (I → Set a) → (p : Level) → Set _
IPred A p = ∀ i → Pred (A i) p

--------------------------------------------------------------------------------
-- Special sets

Uᵢ : IPred Aᵢ zero
Uᵢ x i = ⊤

--------------------------------------------------------------------------------
-- Membership

_∈ᵢ_ : (∀ i → Aᵢ i) → IPred Aᵢ p → Set _
x ∈ᵢ P = ∀ i → x i ∈ P i

_∉ᵢ_ : (∀ i → Aᵢ i) → IPred Aᵢ p → Set _
x ∉ᵢ P = ¬ (x ∈ᵢ P)

--------------------------------------------------------------------------------
-- Relations

subset : ∀ (Aᵢ : I → Set a) → Rel (IPred Aᵢ p) _
subset A P Q = ∀ {x} → x ∈ᵢ P → x ∈ᵢ Q

syntax subset A P Q = P ⊆ᵢ[ A ] Q

⊆-refl : ∀ {p} (Aᵢ : I → Set a) → Reflexive (subset {p = p} Aᵢ)
⊆-refl Aᵢ x i = x i

⊆-trans : ∀ {p} (Aᵢ : I → Set a) → Transitive (subset {p = p} Aᵢ)
⊆-trans Aᵢ x⊆y y⊆z i = y⊆z (x⊆y i)


_⊆ᵢ_ : REL (IPred Aᵢ p) (IPred Aᵢ q) _
P ⊆ᵢ Q = ∀ {i} → P i ⊆ Q i

⊆ᵢ-refl : (Aᵢ : I → Set a) → Reflexive {A = IPred Aᵢ p} _⊆ᵢ_
⊆ᵢ-refl Aᵢ xᵢ∈Pᵢ = xᵢ∈Pᵢ

⊆ᵢ-trans : (Aᵢ : I → Set a) → Transitive {A = IPred Aᵢ p} _⊆ᵢ_
⊆ᵢ-trans Aᵢ P⊆Q Q⊆R = Q⊆R ∘ P⊆Q

_≋ᵢ_ : REL (IPred Aᵢ p) (IPred Aᵢ q) _
p ≋ᵢ q = p ⊆ᵢ q × q ⊆ᵢ p

≋ᵢ-refl : Reflexive {A = IPred Aᵢ p} _≋ᵢ_
≋ᵢ-refl {Aᵢ = Aᵢ} {x = P} = ⊆ᵢ-refl Aᵢ {x = P} , ⊆ᵢ-refl Aᵢ {x = P}

--------------------------------------------------------------------------------
-- Properties

Universalᵢ : Pred (IPred Aᵢ ℓ) _
Universalᵢ P = ∀ {i} x → x ∈ P i

Singletonᵢ : Rel (∀ i → Aᵢ i) ℓ → IPred Aᵢ p → (∀ i → Aᵢ i) → Set _
Singletonᵢ _≈_ P x = (x ∈ᵢ P) × (∀ {y} → y ∈ᵢ P → y ≈ x)

Decidableᵢ : IPred Aᵢ p → Set _
Decidableᵢ P = ∀ x → Dec (x ∈ᵢ P)

Empty : IPred Aᵢ p → Set _
Empty P = ∀ x → x ∉ᵢ P

--------------------------------------------------------------------------------
-- Construction

infixr 7 _∩_
_∩_ : IPred Aᵢ ℓ₁ → IPred Aᵢ ℓ₂ → IPred Aᵢ _
(P ∩ Q) i = λ xᵢ → xᵢ ∈ P i × xᵢ ∈ Q i

infixr 6 _∪_
_∪_ : IPred Aᵢ ℓ₁ → IPred Aᵢ ℓ₂ → IPred Aᵢ _
(P ∪ Q) i = λ xᵢ → xᵢ ∈ P i ⊎ xᵢ ∈ Q i
