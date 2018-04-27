open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Vec
open import Data.List using (List; []; _∷_) renaming (map to mapₗ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Unary using (Pred; Decidable)

module RoutingLib.Data.Vec where

  -- stdlib
  count : ∀ {a p} {A : Set a} {P : Pred A p} → Decidable P →
          ∀ {n} → Vec A n → ℕ
  count P? []       = zero
  count P? (x ∷ xs) with P? x
  ... | yes _ = suc (count P? xs)
  ... | no  _ = count P? xs


  _∉_ : ∀ {a n} {A : Set a} → A → Vec A n → Set a
  v ∉ xs = ¬ (v ∈ xs)

  {-
  foldr₂ : ∀ {a} {A : Set a} {m} → (A → A → A) → A → Vec A m → A
  foldr₂ {A = A} _⊕_ e xs = foldr (λ _ → A) _⊕_ e xs

  foldl₂ : ∀ {a} {A : Set a} {m} → (A → A → A) → A → Vec A m → A
  foldl₂ {A = A} _⊕_ e xs = foldl (λ _ → A) _⊕_ e xs
  -}
