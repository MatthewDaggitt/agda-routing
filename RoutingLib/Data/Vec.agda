open import Data.Nat using (suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Vec
open import Data.List using (List; []; _∷_) renaming (map to mapₗ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module RoutingLib.Data.Vec where

  -----------------------
  -- To push to stdlib --
  -----------------------

  _∉_ : ∀ {a n} {A : Set a} → A → Vec A n → Set a
  v ∉ xs = ¬ (v ∈ xs)

  foldr₂ : ∀ {a} {A : Set a} {m} → (A → A → A) → A → Vec A m → A
  foldr₂ {A = A} _⊕_ e xs = foldr (λ _ → A) _⊕_ e xs

  foldl₂ : ∀ {a} {A : Set a} {m} → (A → A → A) → A → Vec A m → A
  foldl₂ {A = A} _⊕_ e xs = foldl (λ _ → A) _⊕_ e xs


  ---------------------------
  -- Additional operations --
  ---------------------------

  ∉-extend : ∀ {a n} {A : Set a} {v x : A} {xs : Vec A n} → ¬ (v ≡ x) → v ∉ xs → v ∉ (x ∷ xs)
  ∉-extend v≢x v∉xs here         = v≢x refl
  ∉-extend _   v∉xs (there v∈xs) = v∉xs v∈xs

  find : ∀ {a n} {A : Set a} → Decidable (_≡_ {A = A}) → (v : A) (xs : Vec A n) → v ∈ xs ⊎ v ∉ xs
  find _   v [] = inj₂ λ()
  find _≟_ v (x ∷ xs) with v ≟ x | find _≟_ v xs
  ... | yes v≡x | _         rewrite v≡x = inj₁ here
  ... | _       | inj₁ v∈xs = inj₁ (there v∈xs)
  ... | no  v≢x | inj₂ v∉xs = inj₂ (∉-extend v≢x v∉xs)

  findAll : ∀ {a n} {A : Set a} → Decidable (_≡_ {A = A}) → (v : A) (xs : Vec A n) → List (Fin n)
  findAll _ v [] = []
  findAll _≟_ v (x ∷ xs) with v ≟ x
  ... | yes v≡x = fzero ∷ mapₗ fsuc (findAll _≟_ v xs)
  ... | no  v≢x = mapₗ fsuc (findAll _≟_ v xs)

  delete : ∀ {a n} {A : Set a} {v : A} {xs : Vec A (suc n)} → v ∈ xs → Vec A n
  delete {xs = x ∷ xs}     here           = xs
  delete {xs = x ∷ []}     (there ())
  delete {xs = x ∷ y ∷ xs} (there v∈y∷xs) = x ∷ delete v∈y∷xs

  deleteAt : ∀ {a n} {A : Set a} (i : Fin (suc n)) (xs : Vec A (suc n)) → Vec A n
  deleteAt fzero (x ∷ xs) = xs
  deleteAt (fsuc ()) (_ ∷ [])
  deleteAt (fsuc i) (x ∷ y ∷ xs) = x ∷ deleteAt i (y ∷ xs)
