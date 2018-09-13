open import Data.Product using (∃; _×_)
open import Data.Unit using (⊤)
open import Level
open import Relation.Nullary using (¬_)
-- open import Relation.Binary.Indexed.Homogeneous using (Rel)
open import Relation.Binary

module RoutingLib.Relation.Unary.Indexed {i} {I : Set i} where

IPred : ∀ {a} → (I → Set a) → (p : Level) → Set _
IPred A p = ∀ {i} → A i → Set p

--------------------------------------------------------------------------------
-- Special sets

U : ∀ {a} (Aᵢ : I → Set a) → IPred Aᵢ zero
U A x = ⊤

--------------------------------------------------------------------------------
-- Membership

module _ {a} {Aᵢ : I → Set a} where

  _∈_ : ∀ {p} → (∀ i → Aᵢ i) → IPred Aᵢ p → Set _
  x ∈ P = ∀ i → P (x i)

  _∉_ : ∀ {p} → (∀ i → Aᵢ i) → IPred Aᵢ p → Set _
  t ∉ P = ¬ (t ∈ P)

--------------------------------------------------------------------------------
-- Relations

subset : ∀ {a} (Aᵢ : I → Set a) → ∀ {p} → Rel (IPred Aᵢ p) _
subset A P Q = ∀ {x} → x ∈ (λ {i} → P {i}) → x ∈ Q

syntax subset A P Q = P ⊆[ A ] Q

⊆-refl : ∀ {a p} (Aᵢ : I → Set a) → Reflexive (subset Aᵢ {p = p})
⊆-refl Aᵢ x i = x i

⊆-trans : ∀ {a p} (Aᵢ : I → Set a) → Transitive (subset Aᵢ {p = p})
⊆-trans Aᵢ x⊆y y⊆z i = y⊆z (x⊆y i)

--------------------------------------------------------------------------------
-- Properties

IsSingleton : ∀ {a p ℓ} {Aᵢ : I → Set a} → Rel (∀ i → Aᵢ i) ℓ →
            IPred Aᵢ p → (∀ i → Aᵢ i) → Set _
IsSingleton _≈_ P x = (x ∈ P) × (∀ {y} → y ∈ P → y ≈ x)

{-
  _⊂_ : ∀ {p} → Rel (Pred A p) _
  P ⊂ Q = P ⊆ Q × ∃ λ t → t ∈ Q × ¬ (t ∈ P)
-}

{-

  ｛_｝ : S → Predᵤ S p
  ｛ t ｝ = t ≈_

  IsSingleton : ∀ {p} → S → Predᵤ (Pred p) (a ⊔ p ⊔ p)
  IsSingleton t P = t ∈ P × ∀ s → s ∈ P → t ≈ s
-}
