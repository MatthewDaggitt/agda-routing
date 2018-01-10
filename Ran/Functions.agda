-- imports
open import Data.Nat
  using (ℕ; zero; suc; _⊔_; _≤_; _≤?_; _<_; _⊓_; _+_)
open import Data.Fin
  using (Fin; toℕ; inject≤) renaming (zero to fzero; suc to fsuc)
open import Function
  using (_∘_)
open import Data.Product
  using (_×_; _,_; proj₁; proj₂; ∃)
open import Relation.Nullary
  using (yes; no)
open import NatInf
  using (ℕ∞; N; ∞) renaming (_⊓_ to _⊓∞_; _⊔_ to _⊔∞_; _≤_ to _≤∞_; _≟_ to _≟∞_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl)
open import Data.Nat.Properties
  using (≤-trans; n≤1+n; ≤-reflexive; m≤m+n)
open import Algebra.FunctionProperties
  using (Op₂)

open import RoutingLib.Data.Table using (foldr)

module Ran.Functions where

  -- sum of a Fin n function
  sum : ∀ {n} → (Fin n → ℕ) → ℕ
  sum f = foldr _+_ zero f

  max∞ : ∀ {n} → (Fin n → ℕ∞) → ℕ∞
  max∞ f = foldr _⊔∞_ (N zero) f

  min∞ : ∀ {n} → (Fin n → ℕ∞) → ℕ∞
  min∞ f = foldr _⊓∞_ ∞ f
