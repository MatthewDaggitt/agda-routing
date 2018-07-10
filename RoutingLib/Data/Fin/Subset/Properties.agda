open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s; _⊔_; _⊓_; _∸_)
open import Data.Nat.Properties using (≤-refl; ≤-step; ≤-trans; ⊓-monoˡ-≤; ⊓-monoʳ-≤; ⊔-monoˡ-≤; ⊔-monoʳ-≤; n≤1+n; +-∸-assoc; suc-injective; n≮n)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Subset
open import Data.Fin.Subset.Properties
open import Data.Bool using (_≟_)
open import Data.Product using (∃; _,_; proj₂)
open import Data.Sum using ([_,_]′)
open import Data.Vec using ([]; _∷_; here; there; count)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; subst; sym; module ≡-Reasoning)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Fin.Subset
open import RoutingLib.Data.Nat.Properties using (m≤n×m≤o⇒m≤n⊓o; n≤m×o≤m⇒n⊔o≤m)

module RoutingLib.Data.Fin.Subset.Properties where

  ∣p∣≤∣x∷p∣ : ∀ {n} x (p : Subset n)  → ∣ p ∣ ≤ ∣ x ∷ p ∣
  ∣p∣≤∣x∷p∣ x p with x ≟ inside
  ... | yes _ = n≤1+n ∣ p ∣
  ... | no  _ = ≤-refl


  -- Intersection

  module _ {n} (p q : Subset n) where

    ∣p∩q∣≤∣p∣ : ∣ p ∩ q ∣ ≤ ∣ p ∣
    ∣p∩q∣≤∣p∣ = p⊆q⇒∣p∣<∣q∣ (p∩q⊆p p q)

    ∣p∩q∣≤∣q∣ : ∣ p ∩ q ∣ ≤ ∣ q ∣
    ∣p∩q∣≤∣q∣ = p⊆q⇒∣p∣<∣q∣ (p∩q⊆q p q)

    ∣p∩q∣≤∣p∣⊓∣q∣ : ∣ p ∩ q ∣ ≤ ∣ p ∣ ⊓ ∣ q ∣
    ∣p∩q∣≤∣p∣⊓∣q∣ = m≤n×m≤o⇒m≤n⊓o ∣p∩q∣≤∣p∣ ∣p∩q∣≤∣q∣

  p∩∁p≡⊥ : ∀ {n} (p : Subset n) → p ∩ ∁ p ≡ ⊥
  p∩∁p≡⊥ []            = refl
  p∩∁p≡⊥ (outside ∷ p) = cong (outside ∷_) (p∩∁p≡⊥ p)
  p∩∁p≡⊥ (inside  ∷ p) = cong (outside ∷_) (p∩∁p≡⊥ p)

  -- Union

  module _ {n} (p q : Subset n) where

    ∣p∣≤∣p∪q∣ : ∣ p ∣ ≤ ∣ p ∪ q ∣
    ∣p∣≤∣p∪q∣ = p⊆q⇒∣p∣<∣q∣ (p⊆p∪q {p = p} q)

    ∣q∣≤∣p∪q∣ : ∣ q ∣ ≤ ∣ p ∪ q ∣
    ∣q∣≤∣p∪q∣ = p⊆q⇒∣p∣<∣q∣ (q⊆p∪q p q)

    ∣p∣⊔∣q∣≤∣p∪q∣ : ∣ p ∣ ⊔ ∣ q ∣ ≤ ∣ p ∪ q ∣
    ∣p∣⊔∣q∣≤∣p∪q∣ = n≤m×o≤m⇒n⊔o≤m ∣p∣≤∣p∪q∣ ∣q∣≤∣p∪q∣

  p∪∁p≡⊤ : ∀ {n} (p : Subset n) → p ∪ ∁ p ≡ ⊤
  p∪∁p≡⊤ []            = refl
  p∪∁p≡⊤ (outside ∷ p) = cong (inside ∷_) (p∪∁p≡⊤ p)
  p∪∁p≡⊤ (inside  ∷ p) = cong (inside ∷_) (p∪∁p≡⊤ p)


  -- Difference

  p\\q⊆p : ∀ {n} (p q : Subset n) → p \\ q ⊆ p
  p\\q⊆p []            []            ()
  p\\q⊆p (inside  ∷ p) (outside ∷ q) here       = here
  p\\q⊆p (inside  ∷ p) (outside ∷ q) (there x∈) = there (p\\q⊆p p q x∈)
  p\\q⊆p (outside ∷ p) (outside ∷ q) (there x∈) = there (p\\q⊆p p q x∈)
  p\\q⊆p (_       ∷ p) (inside  ∷ q) (there x∈) = there (p\\q⊆p p q x∈)


  module _ {n} (p q : Subset n) where

    ∣p\\q∣≤∣p∣ : ∣ p \\ q ∣ ≤ ∣ p ∣
    ∣p\\q∣≤∣p∣ = p⊆q⇒∣p∣<∣q∣ (p\\q⊆p p q)


  x∷p\\y∷q≡z∷p\\q : ∀ {n} (p q : Subset n) x y → ∃ λ z → z ∷ (p \\ q) ≡ (x ∷ p) \\ (y ∷ q)
  x∷p\\y∷q≡z∷p\\q p q x outside = x       , refl
  x∷p\\y∷q≡z∷p\\q p q x inside  = outside , refl

  ∣p\\q∣<∣p∣ : ∀ {n} {p q : Subset n} → Nonempty (p ∩ q) → ∣ p \\ q ∣ < ∣ p ∣
  ∣p\\q∣<∣p∣ {zero} {[]} {[]} (() , i∈p∩q)
  ∣p\\q∣<∣p∣ {suc n} {outside ∷ p} {y ∷ q} (zero , i∈p∩q) with x∈p∩q⁻ (outside ∷ p) (y ∷ q) i∈p∩q
  ... | () , _
  ∣p\\q∣<∣p∣ {suc n} {inside ∷ p} {outside ∷ q} (zero , i∈p∩q) with x∈p∩q⁻ (inside ∷ p) (outside ∷ q) i∈p∩q
  ... | _ , ()
  ∣p\\q∣<∣p∣ {suc n} {outside ∷ p} {outside ∷ q} (suc i , i∈p∩q) = ∣p\\q∣<∣p∣ {n} {p} {q} (i , drop-there i∈p∩q)
  ∣p\\q∣<∣p∣ {suc n} {outside ∷ p} {inside ∷ q} (suc i , i∈p∩q) = ∣p\\q∣<∣p∣ {n} {p} {q} (i , drop-there i∈p∩q)
  ∣p\\q∣<∣p∣ {suc n} {inside ∷ p} {outside ∷ q} (suc i , i∈p∩q) = s≤s (∣p\\q∣<∣p∣ {n} {p} {q} (i , drop-there i∈p∩q))
  ∣p\\q∣<∣p∣ {suc n} {inside ∷ p} {inside ∷ q} (i , i∈p∩q) = s≤s (∣p\\q∣≤∣p∣ p q)

  ∣p∪⁅i⁆∣≡1+∣p∣ : ∀ {n} {p : Subset n} {i : Fin n} → i ∉ p → ∣ p ∪ ⁅ i ⁆ ∣ ≡ suc ∣ p ∣
  ∣p∪⁅i⁆∣≡1+∣p∣ {_} {outside ∷ p} {zero}  i∉p = cong (λ q → suc ∣ q ∣) (∪-identityʳ p)
  ∣p∪⁅i⁆∣≡1+∣p∣ {_} {inside  ∷ p} {zero}  i∉p = contradiction here i∉p
  ∣p∪⁅i⁆∣≡1+∣p∣ {_} {outside ∷ p} {suc i} i∉p = ∣p∪⁅i⁆∣≡1+∣p∣ (i∉p ∘ there)
  ∣p∪⁅i⁆∣≡1+∣p∣ {_} {inside  ∷ p} {suc i} i∉p = cong suc (∣p∪⁅i⁆∣≡1+∣p∣ (i∉p ∘ there))


  ∣∁p∣≡n∸∣p∣ : ∀ {n} (p : Subset n) → ∣ ∁ p ∣ ≡ n ∸ ∣ p ∣
  ∣∁p∣≡n∸∣p∣ []            = refl
  ∣∁p∣≡n∸∣p∣ (inside  ∷ p) = ∣∁p∣≡n∸∣p∣ p
  ∣∁p∣≡n∸∣p∣ (outside ∷ p) = begin
    suc ∣ ∁ p ∣     ≡⟨ cong suc (∣∁p∣≡n∸∣p∣ p) ⟩
    suc (_ ∸ ∣ p ∣) ≡⟨ sym (+-∸-assoc 1 (∣p∣≤n p)) ⟩
    suc  _ ∸ ∣ p ∣  ∎
    where open ≡-Reasoning

  ∣p∣<n⇒Nonfull : ∀ {n} {p : Subset n} → ∣ p ∣ < n → Nonfull p
  ∣p∣<n⇒Nonfull {p = []}          ()
  ∣p∣<n⇒Nonfull {p = outside ∷ p} _          = zero , λ()
  ∣p∣<n⇒Nonfull {p = inside  ∷ p} (s≤s ∣p∣<n) with ∣p∣<n⇒Nonfull {p = p} ∣p∣<n
  ... | i , i∉p = suc i , λ {(there i∈p) → i∉p i∈p}

  ∣p∣≡n⇒p≡⊤ : ∀ {n} {p : Subset n} → ∣ p ∣ ≡ n → p ≡ ⊤
  ∣p∣≡n⇒p≡⊤ {_} {[]}          _     = refl
  ∣p∣≡n⇒p≡⊤ {n} {outside ∷ p} ∣p∣≡n = contradiction (subst (_< n) ∣p∣≡n (s≤s (∣p∣≤n p))) (n≮n n)
  ∣p∣≡n⇒p≡⊤ {_} {inside  ∷ p} ∣p∣≡n = cong (inside ∷_) (∣p∣≡n⇒p≡⊤ (suc-injective ∣p∣≡n))

  Nonfull⁅i⁆ : ∀ {n} (i : Fin (suc (suc n))) → Nonfull ⁅ i ⁆
  Nonfull⁅i⁆ zero    = suc zero , λ {(there ())}
  Nonfull⁅i⁆ (suc i) = zero     , λ()

  Nonfull⁅i⁆′ : ∀ {n} → 1 < n → (i : Fin n) → Nonfull ⁅ i ⁆
  Nonfull⁅i⁆′ (s≤s (s≤s z≤n)) zero    = suc zero , λ {(there ())}
  Nonfull⁅i⁆′ (s≤s (s≤s z≤n)) (suc i) = zero     , λ()

  i∉p⇒i∉p\\q : ∀ {n} {p : Subset n} {i} → i ∉ p → ∀ q → i ∉ p \\ q
  i∉p⇒i∉p\\q {0} {[]} {i} i∉p [] = ∉⊥
  i∉p⇒i∉p\\q {suc n} {outside ∷ p} {zero} i∉p (outside ∷ q) ()
  i∉p⇒i∉p\\q {suc n} {inside ∷ p} {zero} i∉p (x ∷ q) = contradiction here i∉p
  i∉p⇒i∉p\\q {suc n} {outside ∷ p} {zero} i∉p (inside ∷ q) ()
  i∉p⇒i∉p\\q {suc n} {x ∷ p} {suc i} i∉p (y ∷ q) with x∷p\\y∷q≡z∷p\\q p q x y
  ... | _ , ≡z∷p\\q rewrite (sym ≡z∷p\\q) = (i∉p⇒i∉p\\q {p = p} {i} (i∉p ∘ there) q) ∘ drop-there

  i∉p\\q⇒i∉p : ∀ {n} {p q : Subset n} {i} → i ∉ p \\ q → i ∉ q → i ∉ p
  i∉p\\q⇒i∉p {0}     {[]} {[]} {i} i∉p\\q i∉q = ∉⊥
  i∉p\\q⇒i∉p {suc n} {x ∷ p} {y ∷ q} {suc i} i∉x∷p\\y∷q i∉q (there i∈p) =
    i∉p\\q⇒i∉p i∉p\\q (i∉q ∘ there) i∈p
    where
    i∉p\\q : i ∉ (p \\ q)
    i∉p\\q = i∉x∷p\\y∷q ∘ (λ i∈p\\q → subst (suc i ∈_)
      (proj₂ (x∷p\\y∷q≡z∷p\\q p q x y)) (there i∈p\\q))
  i∉p\\q⇒i∉p {.(suc _)} {inside ∷ p} {outside ∷ q} {zero} i∉p\\q i∉q here = i∉p\\q here
  i∉p\\q⇒i∉p {.(suc _)} {inside ∷ p} {inside ∷ q} {zero} i∉p\\q i∉q here = i∉q here

  i∉⁅j⁆ : ∀ {n} {i j : Fin n} → i ≢ j → i ∉ ⁅ j ⁆
  i∉⁅j⁆ {zero}  {()}
  i∉⁅j⁆ {suc n} {zero}  {zero}  i≢j _             = contradiction refl i≢j
  i∉⁅j⁆ {suc n} {zero}  {suc j} i≢j ()
  i∉⁅j⁆ {suc n} {suc i} {zero}  i≢j (there i∈⁅j⁆) = contradiction i∈⁅j⁆ ∉⊥
  i∉⁅j⁆ {suc n} {suc i} {suc j} i≢j i∈⁅j⁆         = i≢j (x∈⁅y⁆⇒x≡y (suc j) i∈⁅j⁆)

  x∉p∪q⁺ :  ∀ {n} {p q : Subset n} {x} → x ∉ p → x ∉ q → x ∉ p ∪ q
  x∉p∪q⁺ x∉p x∉q = [ x∉p , x∉q ]′ ∘ x∈p∪q⁻ _ _
