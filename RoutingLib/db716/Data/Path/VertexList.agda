
module RoutingLib.db716.Data.Path.VertexList where

open import Data.Fin using (Fin)
open import Data.List using (List ; _∷_; []; length; zip)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; Pointwise-≡⇒≡) renaming (refl to ≈ₚ-refl)
open import Data.Nat using (suc; _≤_; s≤s)
open import Data.Nat.Properties using (≤-reflexive; ≤-trans; <-trans; n≤1+n)
open import Data.Product using (proj₂; _,_; ∃)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import RoutingLib.db716.Data.Path.UncertifiedFinite

toVertexList : ∀ {n} → Path n →  List (Fin n)
toVertexList {n} [] = []
toVertexList {n} ((x , y) ∷ []) = x ∷ y ∷ []
toVertexList {n} ((x , y) ∷ e ∷ p) = x ∷ (toVertexList (e ∷ p))

fromVertexList : ∀ {n} → List (Fin n) → Path n
fromVertexList {n} [] = []
fromVertexList {n} (x ∷ l) = zip (x ∷ l) l

from-toVertexList-≈ₚ : ∀ {n} {p : Path n} → ValidPath p → (fromVertexList (toVertexList p)) ≈ₚ p
from-toVertexList-≈ₚ {n} {[]} valid = []
from-toVertexList-≈ₚ {n} {x ∷ []} valid = refl ∷ []
from-toVertexList-≈ₚ {n} {x ∷ y ∷ []} (continue ∷ valid) = refl ∷ refl ∷ []
from-toVertexList-≈ₚ {n} {x ∷ y ∷ z ∷ p} (continue ∷ valid) = refl ∷ from-toVertexList-≈ₚ valid

from-toVertexList-≡ : ∀ {n} {p : Path n} → ValidPath p → (fromVertexList (toVertexList p)) ≡ p
from-toVertexList-≡ valid = Pointwise-≡⇒≡ (from-toVertexList-≈ₚ valid)

length-toVertexList : ∀ {n} (p : Path n) (x : Edge n) → length (toVertexList (x ∷ p)) ≡ suc (length (x ∷ p))
length-toVertexList {suc n} [] x = refl
length-toVertexList {suc n} (x₁ ∷ p) x = cong suc (length-toVertexList p x₁)

fromVertexList-lookup : ∀ {n} {y : Vertex n} {l : List (Vertex n)} {l0 : Vertex n} → suc 0 ≤ length l → y ∈ l → ∃ λ x → (x , y) ∈ fromVertexList (l0 ∷ l)
fromVertexList-lookup {suc n} {y} {l1 ∷ l} {l0} 1≤l y∈l = zip-∈ʳ (l0 ∷ l1 ∷ l) (l1 ∷ l) y (s≤s (n≤1+n _)) y∈l
  where
    zip-∈ʳ : ∀ {a} {A : Set a} (xs ys : List A) (y : A) → length ys ≤ length xs → y ∈ ys → ∃ λ x → (x , y) ∈ (zip xs ys)
    zip-∈ʳ (x₀ ∷ xs) (y₀ ∷ ys) (y) ys≤xs (here y≡y₀) rewrite y≡y₀ = x₀ , here refl
    zip-∈ʳ (x₀ ∷ xs) (y₀ ∷ ys) (y)(s≤s ys≤xs) (there y∈ys) =
      let x , [x,y]∈zip = zip-∈ʳ xs ys y ys≤xs y∈ys
      in x , there ([x,y]∈zip)
