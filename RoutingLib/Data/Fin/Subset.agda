open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-step)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Subset
open import Data.Fin.Subset.Properties
open import Data.Bool using (_≟_)
open import Data.Product using (∃; _,_; proj₂)
open import Data.Vec using ([]; _∷_; here; there)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; subst; sym)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Vec using (count)

module RoutingLib.Data.Fin.Subset where

  size : ∀ {n} → Subset n → ℕ
  size p = count (_≟ inside) p

  _\\_ : ∀ {n} → Subset n → Subset n → Subset n
  []      \\ _             = []
  (x ∷ p) \\ (inside ∷ q)  = outside ∷ (p \\ q)
  (x ∷ p) \\ (outside ∷ q) = x       ∷ (p \\ q)

  x∷p\\y∷q≡z∷p\\q : ∀ {n} (p q : Subset n) x y → ∃ λ z → z ∷ (p \\ q) ≡ (x ∷ p) \\ (y ∷ q)
  x∷p\\y∷q≡z∷p\\q p q x outside = x       , refl
  x∷p\\y∷q≡z∷p\\q p q x inside  = outside , refl

  size[p\\q]≤size[p] : ∀ {n} (p q : Subset n) → size (p \\ q) ≤ size p
  size[p\\q]≤size[p] [] [] = ≤-refl
  size[p\\q]≤size[p] (outside ∷ p) (outside ∷ q) = size[p\\q]≤size[p] p q
  size[p\\q]≤size[p] (inside ∷ p) (outside ∷ q) = s≤s (size[p\\q]≤size[p] p q)
  size[p\\q]≤size[p] (outside ∷ p) (inside ∷ q) = size[p\\q]≤size[p] p q
  size[p\\q]≤size[p] (inside ∷ p) (inside ∷ q) = ≤-step (size[p\\q]≤size[p] p q)
  
  size[p\\q]<size[p] : ∀ {n} {p q : Subset n} → Nonempty (p ∩ q) → size (p \\ q) < size p
  size[p\\q]<size[p] {zero} {[]} {[]} (() , i∈p∩q)
  size[p\\q]<size[p] {suc n} {outside ∷ p} {y ∷ q} (fzero , i∈p∩q) with x∈p∩q⁻ (outside ∷ p) (y ∷ q) i∈p∩q
  ... | () , _
  size[p\\q]<size[p] {suc n} {inside ∷ p} {outside ∷ q} (fzero , i∈p∩q) with x∈p∩q⁻ (inside ∷ p) (outside ∷ q) i∈p∩q
  ... | _ , ()
  size[p\\q]<size[p] {suc n} {outside ∷ p} {outside ∷ q} (fsuc i , i∈p∩q) =
    size[p\\q]<size[p] {n} {p} {q} (i , drop-there i∈p∩q)
  size[p\\q]<size[p] {suc n} {outside ∷ p} {inside ∷ q} (fsuc i , i∈p∩q) =
    size[p\\q]<size[p] {n} {p} {q} (i , drop-there i∈p∩q)
  size[p\\q]<size[p] {suc n} {inside ∷ p} {outside ∷ q} (fsuc i , i∈p∩q) = s≤s (size[p\\q]<size[p] {n} {p} {q} (i , drop-there i∈p∩q))
  size[p\\q]<size[p] {suc n} {inside ∷ p} {inside ∷ q} (i , i∈p∩q) = s≤s (size[p\\q]≤size[p] p q) 

  i∉p⇒i∉p\\q : ∀ {n} {p : Subset n} {i} → i ∉ p → ∀ q → i ∉ p \\ q
  i∉p⇒i∉p\\q {0} {[]} {i} i∉p [] = ∉⊥
  i∉p⇒i∉p\\q {suc n} {outside ∷ p} {fzero} i∉p (outside ∷ q) ()
  i∉p⇒i∉p\\q {suc n} {inside ∷ p} {fzero} i∉p (x ∷ q) = contradiction here i∉p
  i∉p⇒i∉p\\q {suc n} {outside ∷ p} {fzero} i∉p (inside ∷ q) ()
  i∉p⇒i∉p\\q {suc n} {x ∷ p} {fsuc i} i∉p (y ∷ q) with x∷p\\y∷q≡z∷p\\q p q x y
  ... | _ , ≡z∷p\\q rewrite (sym ≡z∷p\\q) = (i∉p⇒i∉p\\q {p = p} {i} (i∉p ∘ there) q) ∘ drop-there

  i∉p\\q⇒i∉p : ∀ {n} {p q : Subset n} {i} → i ∉ p \\ q → i ∉ q → i ∉ p
  i∉p\\q⇒i∉p {0}     {[]} {[]} {i} i∉p\\q i∉q = ∉⊥
  i∉p\\q⇒i∉p {suc n} {x ∷ p} {y ∷ q} {fsuc i} i∉x∷p\\y∷q i∉q (there i∈p) =
    i∉p\\q⇒i∉p i∉p\\q (i∉q ∘ there) i∈p
    where
    i∉p\\q : i ∉ (p \\ q)
    i∉p\\q = i∉x∷p\\y∷q ∘ (λ i∈p\\q → subst (fsuc i ∈_)
      (proj₂ (x∷p\\y∷q≡z∷p\\q p q x y)) (there i∈p\\q))
  i∉p\\q⇒i∉p {.(suc _)} {inside ∷ p} {outside ∷ q} {fzero} i∉p\\q i∉q here = i∉p\\q here
  i∉p\\q⇒i∉p {.(suc _)} {inside ∷ p} {inside ∷ q} {fzero} i∉p\\q i∉q here = i∉q here
  

  i∉⁅j⁆ : ∀ {n} {i j : Fin n} → i ≢ j → i ∉ ⁅ j ⁆
  i∉⁅j⁆ {zero} {()}     _   _
  i∉⁅j⁆ {suc n} {fzero} {fzero} i≢j _ = contradiction refl i≢j
  i∉⁅j⁆ {suc n} {fzero} {fsuc j} i≢j ()
  i∉⁅j⁆ {suc n} {fsuc i} {fzero} i≢j (there i∈⁅j⁆) = contradiction i∈⁅j⁆ ∉⊥
  i∉⁅j⁆ {suc n} {fsuc i} {fsuc j} i≢j i∈⁅j⁆ = i≢j (x∈⁅y⁆⇒x≡y (fsuc j) i∈⁅j⁆)
