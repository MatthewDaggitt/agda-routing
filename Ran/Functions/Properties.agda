-- imports
open import Functions
open import Data.Nat
  using (ℕ; zero; suc; _≤_; _<_; _+_; _⊔_; _⊓_; z≤n; _*_)
open import Data.Fin
  using (Fin; toℕ; inject≤) renaming (zero to fzero; suc to fsuc)
open import Data.Product
  using (proj₁; ∃; _,_)
open import NatInf
  using (ℕ∞) renaming (_≤_ to _≤∞_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; subst; refl)
open import Level
  using () renaming (zero to lzero)
open import Relation.Unary
  using (Pred)
open import Algebra.FunctionProperties
  using (Op₂)
open import Function
  using (_∘_)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
open import Data.Nat.Properties
  using (m⊓n≤m; ≤-antisym; ⊔-sel)

module Ran.Functions.Properties where


  -- properties of max and min
  postulate min∞-monotone : ∀ {n f g} → (∀ i → f i ≤∞ g i) → min∞ {n} f ≤∞ min∞ {n} g
  postulate min∞-dec : ∀ {n} f i → min∞ {n} f ≤∞ f i
  postulate min∞-equiv : ∀ {n g h} → (∀ i → g i ≡ h i) → min∞ {n} g ≡ min∞ {n} h


  -- properties of sum
  postulate sum-inc : ∀ {n f g} → (∀ i → f i ≤ g i) → sum {n} f ≤ sum {n} g
  postulate sum-inc-strict : ∀ {n f g} → (∀ i → f i ≤ g i) → ∃ (λ i → f i < g i)
                             → sum {n} f < sum {n} g
  postulate sum-limit : ∀ {n f x} → (∀ i → f i ≤ x) → sum {n} f ≤ x * n
  postulate x≤sum : ∀ {n i} f → f i ≤ sum {n} f
  postulate x+y≤sum² : ∀ {n} i j k (f : Fin n → Fin n → ℕ∞) (g : ℕ∞ → ℕ) →
                       g (f i k) + g (f k j) ≤ sum {n} (λ i₁ → sum {n} (λ j₁ → g (f i j)))
