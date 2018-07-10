open import Data.Product using (∃; _×_)
open import Level
open import Relation.Nullary using (¬_)
-- open import Relation.Binary.Indexed.Homogeneous using (Rel)
open import Relation.Binary using (Rel)

module RoutingLib.Relation.Unary.Indexed  where

Pred : ∀ {i a} {I : Set i} → (I → Set a) → (ℓ : Level) → Set _
Pred A ℓ = ∀ {i} → A i → Set ℓ

module _ {i a} {I : Set i} {A : I → Set a} where

  _∈_ : ∀ {ℓ} → (∀ i → A i) → Pred A ℓ → Set _
  x ∈ P = ∀ i → P (x i)

  _∉_ : ∀ {ℓ} → (∀ i → A i) → Pred A ℓ → Set _
  t ∉ P = ¬ (t ∈ P)

  _⊆_ : ∀ {ℓ} → Rel (Pred A ℓ) _
  P ⊆ Q = ∀ {x} → x ∈ P → x ∈ Q

--∀ {x} → x ∈ P → x ∈ Q
{-
  _⊂_ : ∀ {ℓ} → Rel (Pred A ℓ) _
  P ⊂ Q = P ⊆ Q × ∃ λ t → t ∈ Q × ¬ (t ∈ P)
-}

{-

  ｛_｝ : S → Predᵤ S ℓ
  ｛ t ｝ = t ≈_

  IsSingleton : ∀ {p} → S → Predᵤ (Pred p) (a ⊔ p ⊔ ℓ)
  IsSingleton t P = t ∈ P × ∀ s → s ∈ P → t ≈ s
-}
