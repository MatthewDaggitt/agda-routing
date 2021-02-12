open import Algebra using (Semiring)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Fin using (Fin; suc; zero; punchIn)
open import Data.Product using (∃; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Vec.Functional using (Vector; foldr; tail)
open import Function using (_∘_)

open import RoutingLib.Data.Matrix

-- Properties of sums over Tables of Semirings
module RoutingLib.db716.Algebra.Properties.Summation {c ℓ} (S : Semiring c ℓ) where

open Semiring S renaming (Carrier to C)

open import Relation.Binary.Reasoning.Setoid setoid

-- Definitions for vectors and summation
private Vec : ∀ (n : ℕ) →  Set c
Vec n = Vector C n

∑ : ∀ {n} → Vec n → C
∑ {n} v = foldr _+_ 0# v

∑0≈0 : ∀ {n : ℕ} (v : Vec n) → (∀ i → v i ≈ 0#) → ∑ v ≈ 0#
∑0≈0 {zero} v eq = refl
∑0≈0 {suc n} v eq = trans (+-cong (eq Fin.zero) (∑0≈0 (tail v) (eq ∘ suc))) (+-identityˡ 0#)

∑0*v≈0 : ∀ {n : ℕ} (v : Vec n) → ∑ (λ i → 0# * v i) ≈ 0#
∑0*v≈0 v = ∑0≈0 (λ i → 0# * v i) (zeroˡ ∘ v)

∑v*0≈0 : ∀ {n : ℕ} (v : Vec n) → ∑ (λ i → v i * 0#) ≈ 0#
∑v*0≈0 v = ∑0≈0 (λ i → v i * 0#) (zeroʳ ∘ v)

∑-cong : ∀ {n : ℕ} {u v : Vec n} → (∀ i → u i ≈ v i) → (∑ u) ≈ (∑ v)
∑-cong {zero} _ = refl
∑-cong {suc n} eq = +-cong (eq Fin.zero) (∑-cong (eq ∘ suc))

∑-distˡ : {n : ℕ} (v : Vec n) (c : C) → c * (∑ v) ≈ ∑ (λ i → c * v i)
∑-distˡ {zero} _ c = zeroʳ c
∑-distˡ {suc n} v c = trans (distribˡ c _ _) ( +-cong (refl) (∑-distˡ (tail v) c))

∑-distʳ : {n : ℕ} (v : Vec n) (c : C) → (∑ v) * c ≈ ∑ (λ i → v i * c)
∑-distʳ {zero} _ c = zeroˡ c
∑-distʳ {suc n} v c = trans (distribʳ c _ _) ( +-cong (refl) (∑-distʳ (tail v) c))

∑-reassoc : {n : ℕ} (u v : Vec n) → ∑ u + ∑ v ≈ ∑ (λ i → u i + v i)
∑-reassoc {zero} _ _ = +-identityˡ 0#
∑-reassoc {suc n} u v = begin
  (u Fin.zero + ∑ (tail u)) + (v Fin.zero + ∑ (tail v))  ≈˘⟨ +-assoc _ _ _ ⟩
  ((u Fin.zero + ∑ (tail u)) + v Fin.zero) + ∑ (tail v)  ≈⟨ +-cong (+-assoc _ _ _) refl ⟩
  (u Fin.zero + (∑ (tail u) + v Fin.zero)) + ∑ (tail v)  ≈⟨ +-cong (+-cong refl (+-comm _ _)) refl ⟩
  (u Fin.zero + (v Fin.zero + ∑ (tail u))) + ∑ (tail v)  ≈⟨ +-cong (sym (+-assoc _ _ _)) refl ⟩
  ((u Fin.zero + v Fin.zero) + ∑ (tail u)) + ∑ (tail v)  ≈⟨ +-assoc _ _ _ ⟩
  (u Fin.zero + v Fin.zero) + (∑ (tail u) + ∑ (tail v))  ≈⟨ +-cong refl (∑-reassoc (tail u) (tail v)) ⟩
  (u Fin.zero + v Fin.zero) + ∑ (tail (λ i → u i + v i)) ∎

-- We can swap the sums in double summations.
∑-comm : {n : ℕ} (v : SquareMatrix C n) → ∑ (λ i → ∑ (row i v)) ≈ ∑ (λ j → ∑ (col j v))
∑-comm {zero} v = refl
∑-comm {suc n} v = begin
  v Fin.zero Fin.zero + ∑ (λ i → v Fin.zero (suc i)) + ∑ (λ i → ∑ (v (suc i)))
    ≈˘⟨  +-cong refl (∑-reassoc (tail (col Fin.zero v)) _) ⟩
  v Fin.zero Fin.zero + ∑ (λ i → v Fin.zero (suc i)) + (∑ (λ i → v (suc i) Fin.zero) + ∑ (λ i → ∑ (λ j → v (suc i) (suc j))))
    ≈˘⟨ +-assoc _ _ _  ⟩
  v Fin.zero Fin.zero + ∑ (λ i → v Fin.zero (suc i)) + ∑ (λ i → v (suc i) Fin.zero) + ∑ (λ i → ∑ (λ j → v (suc i) (suc j)))
    ≈⟨ +-cong (+-assoc _ _ _) refl ⟩
  v Fin.zero Fin.zero + (∑ (λ i → v Fin.zero (suc i)) + ∑ (λ i → v (suc i) Fin.zero)) + ∑ (λ i → ∑ (λ j → v (suc i) (suc j)))
    ≈⟨  +-cong (+-cong refl (+-comm _ _)) refl ⟩
  v Fin.zero Fin.zero + (∑ (λ i → v (suc i) Fin.zero) + ∑ (λ i → v Fin.zero (suc i))) + ∑ (λ i → ∑ (λ j → v (suc i) (suc j)))
    ≈˘⟨ +-cong (+-assoc _ _ _) refl  ⟩
  v Fin.zero Fin.zero + ∑ (λ i → v (suc i) Fin.zero) + ∑ (λ i → v Fin.zero (suc i)) + ∑ (λ i → ∑ (λ j → v (suc i) (suc j)))
    ≈⟨ +-assoc _ _ _ ⟩
  v Fin.zero Fin.zero + ∑ (λ i → v (suc i) Fin.zero) + (∑ (λ i → v Fin.zero (suc i)) + ∑ (λ i → ∑ (λ j → v (suc i) (suc j))))
    ≈⟨ +-cong refl (+-cong refl (∑-comm (λ i j → v (suc i) (suc j)))) ⟩
  v Fin.zero Fin.zero + ∑ (λ i → v (suc i) Fin.zero) + (∑ (λ j → v Fin.zero (suc j)) + ∑ (λ j → ∑ (λ i → v (suc i) (suc j))))
    ≈⟨ +-cong refl (∑-reassoc (tail (v Fin.zero)) _) ⟩
  ∑ (λ j → ∑ (λ i → v i j)) ∎

-- Sometimes useful in place of subtraction
unadd : ∀ {n} (v : Vec (suc n)) (i : Fin (suc n)) → ∃[ x ] (∑ v ≈ x + v i)
unadd {ℕ.zero} v Fin.zero = 0# , +-comm _ _
unadd {suc n} v zero = ∑ (λ x → v (suc x)) , +-comm _ _
unadd {suc n} v (suc i) = x' , proof
  where x = unadd (λ j → v (suc j)) i
        x' = v Fin.zero + (proj₁ x)
        proof : ∑ v ≈ x' + v (suc i)
        proof = begin
          v Fin.zero + ∑ (λ x → v (suc x)) ≈⟨ +-cong refl (proj₂ x) ⟩
          v Fin.zero + ((proj₁ x) + v (suc i)) ≈˘⟨ +-assoc _ _ _ ⟩
          x' + v (suc i) ∎
