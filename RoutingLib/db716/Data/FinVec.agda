open import Algebra using (Monoid)
open import Data.Fin using (Fin; suc) renaming (zero to z)
open import Data.Nat using (ℕ) renaming (suc to sucₙ)
open import Function using (_∘_)

{- 
  TODO: Generalise this to not require a  monoid, 
        use fold instead of sum etc?
-}
module RoutingLib.db716.Data.FinVec {c ℓ} (Mon : Monoid c ℓ) where

  open Monoid Mon using (_∙_; ε; _≈_; ∙-cong) renaming (Carrier to M; refl to ≈-refl)
  
  FinVec : (n : ℕ) → Set _
  FinVec n = Fin n → M

  _≈ᵥ_ : {n : ℕ} → FinVec n → FinVec n → Set _
  u ≈ᵥ v = ∀ i → (u i) ≈ (v i)

  zeroes : {n : ℕ} → FinVec n
  zeroes _ = ε

  tail : {n : ℕ} → FinVec (sucₙ n) → FinVec n
  tail v = λ i → v (suc i)

  _×_ : {n : ℕ} → FinVec n → FinVec n → FinVec n
  u × v = λ i → u i ∙ v i

  _⋉_ : {n : ℕ} → M → FinVec n → FinVec n
  m ⋉ v = λ i → m ∙ (v i)

  _⋊_ : {n : ℕ} → FinVec n → M → FinVec n
  v ⋊ m = λ i → (v i) ∙ m
  
  accum : {n : ℕ} → FinVec n → M
  accum {0} _ = ε
  accum {sucₙ n} v = (v z) ∙ accum (tail v)

  accum-cong : ∀ {n : ℕ} {u v : FinVec n} → u ≈ᵥ v → (accum u) ≈ (accum v)
  accum-cong {0} _ = ≈-refl
  accum-cong {sucₙ n} eq = ∙-cong (eq z) (accum-cong (eq ∘ suc))
