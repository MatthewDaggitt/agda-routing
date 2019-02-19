open import Algebra using (Semiring)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Fin using (Fin; suc; zero; punchIn)
open import Data.Product using (∃; ∃-syntax; _,_; proj₁; proj₂)
open import Function using (_∘_)

open import RoutingLib.Data.Matrix using (SquareMatrix)
open import RoutingLib.Data.Table using (Table; foldr)

open import RoutingLib.db716.Data.Matrix using (row; col)
open import RoutingLib.db716.Data.Table using (tail)

-- Properties of sums over Tables of Semirings
module RoutingLib.db716.Algebra.Properties.Summation {c ℓ} (S : Semiring c ℓ) where

open Semiring S renaming (Carrier to C)

open import Relation.Binary.EqReasoning setoid

-- Definitions for vectors and summation
private Vec : ∀ (n : ℕ) →  Set c
Vec n = Table C n

∑ = foldr _+_ 0#

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
  (u Fin.zero + ∑ (tail u)) + (v Fin.zero + ∑ (tail v))  ≈⟨ sym (+-assoc _ _ _) ⟩
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
    ≈⟨  +-cong refl (sym (∑-reassoc (tail (col Fin.zero v)) _)) ⟩
  v Fin.zero Fin.zero + ∑ (λ i → v Fin.zero (suc i)) + (∑ (λ i → v (suc i) Fin.zero) + ∑ (λ i → ∑ (λ j → v (suc i) (suc j))))
    ≈⟨ sym (+-assoc _ _ _)  ⟩
  v Fin.zero Fin.zero + ∑ (λ i → v Fin.zero (suc i)) + ∑ (λ i → v (suc i) Fin.zero) + ∑ (λ i → ∑ (λ j → v (suc i) (suc j)))
    ≈⟨ +-cong (+-assoc _ _ _) refl ⟩
  v Fin.zero Fin.zero + (∑ (λ i → v Fin.zero (suc i)) + ∑ (λ i → v (suc i) Fin.zero)) + ∑ (λ i → ∑ (λ j → v (suc i) (suc j)))
    ≈⟨  +-cong (+-cong refl (+-comm _ _)) refl ⟩
  v Fin.zero Fin.zero + (∑ (λ i → v (suc i) Fin.zero) + ∑ (λ i → v Fin.zero (suc i))) + ∑ (λ i → ∑ (λ j → v (suc i) (suc j)))
    ≈⟨ +-cong (sym (+-assoc _ _ _)) refl  ⟩
  v Fin.zero Fin.zero + ∑ (λ i → v (suc i) Fin.zero) + ∑ (λ i → v Fin.zero (suc i)) + ∑ (λ i → ∑ (λ j → v (suc i) (suc j)))
    ≈⟨  +-assoc _ _ _ ⟩
  v Fin.zero Fin.zero + ∑ (λ i → v (suc i) Fin.zero) + (∑ (λ i → v Fin.zero (suc i)) + ∑ (λ i → ∑ (λ j → v (suc i) (suc j))))
    ≈⟨ +-cong refl (+-cong refl (∑-comm (λ i j → v (suc i) (suc j)))) ⟩
  v Fin.zero Fin.zero + ∑ (λ i → v (suc i) Fin.zero) + (∑ (λ j → v Fin.zero (suc j)) + ∑ (λ j → ∑ (λ i → v (suc i) (suc j))))
    ≈⟨ +-cong refl (∑-reassoc (tail (v Fin.zero)) _) ⟩
  ∑ (λ j → ∑ (λ i → v i j)) ∎

-- Sometimes useful in place of subtraction
unadd : ∀ {n} (v : Vec (suc n)) (i : Fin (suc n)) → ∃[ x ] (∑ v ≈ x + v i)
unadd {ℕ.zero} v Fin.zero = 0# , +-comm _ _
unadd {ℕ.zero} v (suc ())
unadd {suc n} v zero = ∑ (λ x → v (suc x)) , +-comm _ _
unadd {suc n} v (suc i) = x' , proof
  where x = unadd (λ j → v (suc j)) i
        x' = v Fin.zero + (proj₁ x)
        proof : ∑ v ≈ x' + v (suc i)
        proof = begin
          v Fin.zero + ∑ (λ x → v (suc x)) ≈⟨ +-cong refl (proj₂ x) ⟩
          v Fin.zero + ((proj₁ x) + v (suc i)) ≈⟨ sym (+-assoc _ _ _) ⟩
          x' + v (suc i) ∎

{-
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.N-ary

private append : ∀ {a} {A : Set a} {k : ℕ} → Table A k → A → Table A (suc k)
append v x Fin.zero = x
append v x (suc n) = v n

-- A sum over k+1 indices, each ranging over Fin n
∑⋯∑ : ∀ {n : ℕ} {k : ℕ} → (Vec (Fin n) k →  C) → C
∑⋯∑ {n} {zero} f = f []
--∑⋯∑ {n} {suc zero} f = ∑ (curryⁿ f)
∑⋯∑ {n} {suc k} f = ∑ (λ i → ∑⋯∑ (λ v → f (i ∷ v)))

∑⋯∑-distˡ : ∀ {n k : ℕ} (f : Vec (Fin n) (k) → C) (c : C) → c * (∑⋯∑ f) ≈ ∑⋯∑ (λ v → c * f v)
∑⋯∑-distˡ {n} {ℕ.zero} f c = refl --∑-distˡ (curryⁿ f) c
∑⋯∑-distˡ {n} {suc k} f c = begin
  c * (∑⋯∑ f) ≈⟨ ∑-distˡ (λ i → ∑⋯∑ (λ v → f (i ∷ v))) c ⟩
  ∑ (λ i → c * ∑⋯∑ (λ v → f (i ∷ v))) ≈⟨ ∑-cong (λ i → ∑⋯∑-distˡ {n} {k} (λ v → f (i ∷ v)) c) ⟩
  ∑⋯∑ (λ v → c * (f v)) ∎

∑⋯∑-distʳ : ∀ {n k : ℕ} (f : Vec (Fin n) (suc k) → C) (c : C) → (∑⋯∑ f) * c ≈ ∑⋯∑ (λ v → (f v) * c)
∑⋯∑-distʳ {n} {zero} f c = ∑-distʳ (curryⁿ f) c 
∑⋯∑-distʳ {n} {suc k} f c = begin
  (∑⋯∑ f) * c ≈⟨  ∑-distʳ (λ i → ∑⋯∑ (λ v → f (i ∷ v))) c ⟩
  ∑ (λ i → ∑⋯∑ (λ v → f (i ∷ v)) * c) ≈⟨ ∑-cong (λ i → ∑⋯∑-distʳ {n} {k} (λ v → f (i ∷ v)) c) ⟩
  ∑⋯∑ (λ v → (f v) * c) ∎

∑⋯∑-cong : ∀ {n k : ℕ} {f g : Vec (Fin n) (suc k) → C} → (∀ v → f v ≈ g v) → ∑⋯∑ f ≈ ∑⋯∑ g
∑⋯∑-cong {n} {ℕ.zero} f≈g = ∑-cong (λ i → f≈g (i ∷ []))
∑⋯∑-cong {n} {suc k} f≈g = ∑-cong (λ i → ∑⋯∑-cong (λ v → f≈g (i ∷ v)))

unadd' : ∀ {n k} (f : Vec (Fin (suc n)) (suc k) → C) (v : Vec (Fin (suc n)) (suc k)) → ∃[ x ] (∑⋯∑ f ≈ x + f v)
unadd' {ℕ.zero} {ℕ.zero} f (Fin.zero ∷ []) = 0# , +-comm _ _
unadd' {ℕ.zero} {ℕ.zero} f ((suc ()) ∷ [])
unadd' {suc n} {ℕ.zero} f (Fin.zero ∷ []) = ∑ (λ x → f ((suc x) ∷ [])) , +-comm _ _
unadd' {suc n} {ℕ.zero} f (suc i ∷ []) = x' , proof
  where x = unadd' (λ {(j ∷ []) → f ((suc j) ∷ [])}) (i ∷ []) 
        x' = f (Fin.zero ∷ []) + (proj₁ x)
        proof = begin
          f (Fin.zero ∷ []) + ∑ (λ x → f ((suc x) ∷ [])) ≈⟨  +-cong refl (proj₂ x) ⟩
          f (Fin.zero ∷ []) + ((proj₁ x) + f ((suc i) ∷ [])) ≈⟨ sym (+-assoc _ _ _) ⟩
          x' + f ((suc i) ∷ []) ∎
unadd' {n} {suc k} f (v ∷ vs) = x'' , proof
  where x = λ i → unadd' (λ u → f (i ∷ u)) vs
        x' = unadd (λ i → proj₁ (x i) + f (i ∷ vs)) v
        x'' = proj₁ x' + proj₁ (x v)
        proof = begin
          ∑ (λ i → ∑⋯∑ (λ u → f (i ∷ u))) ≈⟨ ∑-cong (λ i → proj₂ (x i)) ⟩
          ∑ (λ i → (proj₁ (x i)) + f (i ∷ vs)) ≈⟨ proj₂ x' ⟩
          proj₁ x' + ((proj₁ (x v)) + (f (v ∷ vs))) ≈⟨ sym (+-assoc _ _ _) ⟩
          x'' + f (v ∷ vs) ∎
-}
