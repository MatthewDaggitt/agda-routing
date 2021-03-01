open import Algebra using (Semiring)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Fin using (Fin; suc; zero)
open import Data.Product using (∃; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Vec.Functional using (Vector; foldr; tail)
open import Function using (_∘_)

open import RoutingLib.Data.Matrix

module RoutingLib.Algebra.Properties.Semiring.Sum {c ℓ} (S : Semiring c ℓ) where

open Semiring S renaming (Carrier to A)
open import Algebra.Properties.CommutativeMonoid.Sum +-commutativeMonoid as SumProperties public
  using () renaming (sum to ∑)

-- Definitions for vectors and summation

∑0≈0 : ∀ {n : ℕ} (v : Vector A n) → (∀ i → v i ≈ 0#) → ∑ v ≈ 0#
∑0≈0 {zero} v eq = refl
∑0≈0 {suc n} v eq = trans (+-cong (eq Fin.zero) (∑0≈0 (tail v) (eq ∘ suc))) (+-identityˡ 0#)

∑-distˡ : {n : ℕ} (v : Vector A n) (c : A) → c * (∑ v) ≈ ∑ (λ i → c * v i)
∑-distˡ {zero} _ c = zeroʳ c
∑-distˡ {suc n} v c = trans (distribˡ c _ _) ( +-cong (refl) (∑-distˡ (tail v) c))

∑-distʳ : {n : ℕ} (v : Vector A n) (c : A) → (∑ v) * c ≈ ∑ (λ i → v i * c)
∑-distʳ {zero} _ c = zeroˡ c
∑-distʳ {suc n} v c = trans (distribʳ c _ _) ( +-cong (refl) (∑-distʳ (tail v) c))
