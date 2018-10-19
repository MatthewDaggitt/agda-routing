open import Data.Product using (∃; _×_)
open import Data.Unit using (⊤)
open import Level
open import Relation.Nullary using (¬_)
open import Relation.Unary as U using (Pred)
open import Relation.Binary

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

  member : ∀ {p} i → Aᵢ i → IPred Aᵢ p → Set _
  member i xᵢ P = P i xᵢ

  syntax member i xᵢ P = xᵢ ∈[ i ] P
  
--------------------------------------------------------------------------------
-- Relations

subset : ∀ {a} (Aᵢ : I → Set a) → ∀ {p} → Rel (IPred Aᵢ p) _
subset A P Q = ∀ {x} → x ∈ P → x ∈ Q

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
