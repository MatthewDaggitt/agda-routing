open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s; _⊔_; _⊓_; _∸_)
open import Data.Nat.Properties hiding (_≟_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (¬∀⟶∃¬)
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

private
  variable
    n : ℕ
    x y : Fin n
    p q r : Subset n

------------------------------------------------------------------------
-- Cons

∣p∣≤∣x∷p∣ : ∀ {n} x (p : Subset n)  → ∣ p ∣ ≤ ∣ x ∷ p ∣
∣p∣≤∣x∷p∣ x p with x ≟ inside
... | yes _ = n≤1+n ∣ p ∣
... | no  _ = ≤-refl

------------------------------------------------------------------------
-- ⊤

⊤-full : ∀ {n} → Full {n} ⊤
⊤-full zero    = here
⊤-full (suc i) = there (⊤-full i)

∣p∣≡n⇒p≡⊤ : ∀ {n} {p : Subset n} → ∣ p ∣ ≡ n → p ≡ ⊤
∣p∣≡n⇒p≡⊤ {p = []}          _     = refl
∣p∣≡n⇒p≡⊤ {p = outside ∷ p} |p|≡n = contradiction |p|≡n (<⇒≢ (s≤s (∣p∣≤n p)))
∣p∣≡n⇒p≡⊤ {p = inside  ∷ p} |p|≡n = cong (inside ∷_) (∣p∣≡n⇒p≡⊤ (suc-injective |p|≡n))

∣p∣<n⇒Nonfull : ∀ {n} {p : Subset n} → ∣ p ∣ < n → Nonfull p
∣p∣<n⇒Nonfull {p = []}          ()
∣p∣<n⇒Nonfull {p = outside ∷ p} |p|<n       full = contradiction (full zero) λ()
∣p∣<n⇒Nonfull {p = inside  ∷ p} (s≤s |p|<n) full = ∣p∣<n⇒Nonfull |p|<n (drop-there ∘ full ∘ suc)

Nonfull-witness : ∀ {n} {p : Subset n} → Nonfull p → ∃ λ i → i ∉ p
Nonfull-witness {n} {p} ¬pᶠ = ¬∀⟶∃¬ n (_∈ p) (_∈? p) ¬pᶠ

------------------------------------------------------------------------
-- ⁅_⁆

i∉⁅j⁆ : ∀ {n} {i j : Fin n} → i ≢ j → i ∉ ⁅ j ⁆
i∉⁅j⁆ {zero}  {()}
i∉⁅j⁆ {suc n} {zero}  {zero}  i≢j _             = contradiction refl i≢j
i∉⁅j⁆ {suc n} {zero}  {suc j} i≢j ()
i∉⁅j⁆ {suc n} {suc i} {zero}  i≢j (there i∈⁅j⁆) = contradiction i∈⁅j⁆ ∉⊥
i∉⁅j⁆ {suc n} {suc i} {suc j} i≢j i∈⁅j⁆         = i≢j (x∈⁅y⁆⇒x≡y (suc j) i∈⁅j⁆)

Nonfull⁅i⁆ : ∀ {n} (i : Fin (suc (suc n))) → Nonfull ⁅ i ⁆
Nonfull⁅i⁆ zero    full = ∉⊥ (drop-there (full (suc zero)))
Nonfull⁅i⁆ (suc i) full = contradiction (full zero) λ()

Nonfull⁅i⁆′ : ∀ {n} → 1 < n → (i : Fin n) → Nonfull ⁅ i ⁆
Nonfull⁅i⁆′ (s≤s (s≤s 1<n)) = Nonfull⁅i⁆

------------------------------------------------------------------------
-- Complement

x∉p⇒x∈∁p : ∀ {n x} {p : Subset n} → x ∉ p → x ∈ ∁ p
x∉p⇒x∈∁p {_} {()}    {[]}
x∉p⇒x∈∁p {_} {zero}  {outside ∷ p} x∉p = here
x∉p⇒x∈∁p {_} {zero}  {inside ∷ p}  x∉p = contradiction here x∉p
x∉p⇒x∈∁p {_} {suc x} {v ∷ p}       x∉p = there (x∉p⇒x∈∁p (x∉p ∘ there))

x∈p⇒x∉∁p : ∀ {n x} {p : Subset n} → x ∈ p → x ∉ ∁ p
x∈p⇒x∉∁p here        = λ()
x∈p⇒x∉∁p (there x∈p) = x∈p⇒x∉∁p x∈p ∘ drop-there

p∩∁p≡⊥ : ∀ {n} (p : Subset n) → p ∩ ∁ p ≡ ⊥
p∩∁p≡⊥ []            = refl
p∩∁p≡⊥ (outside ∷ p) = cong (outside ∷_) (p∩∁p≡⊥ p)
p∩∁p≡⊥ (inside  ∷ p) = cong (outside ∷_) (p∩∁p≡⊥ p)

------------------------------------------------------------------------
-- Membership

∉-contract : ∀ {n} {i : Fin n} {p} → i ∉ p → ∀ {x} → suc i ∉ x ∷ p
∉-contract ∉p (there ∈p) = ∉p ∈p

------------------------------------------------------------------------
-- Intersection

module _ {n} (p q : Subset n) where

  ∣p∩q∣≤∣p∣ : ∣ p ∩ q ∣ ≤ ∣ p ∣
  ∣p∩q∣≤∣p∣ = p⊆q⇒∣p∣<∣q∣ (p∩q⊆p p q)

  ∣p∩q∣≤∣q∣ : ∣ p ∩ q ∣ ≤ ∣ q ∣
  ∣p∩q∣≤∣q∣ = p⊆q⇒∣p∣<∣q∣ (p∩q⊆q p q)

  ∣p∩q∣≤∣p∣⊓∣q∣ : ∣ p ∩ q ∣ ≤ ∣ p ∣ ⊓ ∣ q ∣
  ∣p∩q∣≤∣p∣⊓∣q∣ = m≤n×m≤o⇒m≤n⊓o ∣p∩q∣≤∣p∣ ∣p∩q∣≤∣q∣

------------------------------------------------------------------------
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

x∉p∪q⁺ :  ∀ {n} {p q : Subset n} {x} → x ∉ p → x ∉ q → x ∉ p ∪ q
x∉p∪q⁺ x∉p x∉q = [ x∉p , x∉q ]′ ∘ x∈p∪q⁻ _ _

------------------------------------------------------------------------
-- Difference

p─q⊆p : ∀ {n} (p q : Subset n) → p ─ q ⊆ p
p─q⊆p []            []            ()
p─q⊆p (inside  ∷ p) (outside ∷ q) here       = here
p─q⊆p (inside  ∷ p) (outside ∷ q) (there x∈) = there (p─q⊆p p q x∈)
p─q⊆p (outside ∷ p) (outside ∷ q) (there x∈) = there (p─q⊆p p q x∈)
p─q⊆p (_       ∷ p) (inside  ∷ q) (there x∈) = there (p─q⊆p p q x∈)


module _ {n} (p q : Subset n) where

  ∣p─q∣≤∣p∣ : ∣ p ─ q ∣ ≤ ∣ p ∣
  ∣p─q∣≤∣p∣ = p⊆q⇒∣p∣<∣q∣ (p─q⊆p p q)

x∷p─y∷q≡z∷p─q : ∀ {n} (p q : Subset n) x y → ∃ λ z → z ∷ (p ─ q) ≡ (x ∷ p) ─ (y ∷ q)
x∷p─y∷q≡z∷p─q p q x outside = x       , refl
x∷p─y∷q≡z∷p─q p q x inside  = outside , refl

∣p─q∣<∣p∣ : ∀ {n} {p q : Subset n} → Nonempty (p ∩ q) → ∣ p ─ q ∣ < ∣ p ∣
∣p─q∣<∣p∣ {zero} {[]} {[]} (() , i∈p∩q)
∣p─q∣<∣p∣ {suc n} {outside ∷ p} {y ∷ q} (zero , i∈p∩q) with x∈p∩q⁻ (outside ∷ p) (y ∷ q) i∈p∩q
... | () , _
∣p─q∣<∣p∣ {suc n} {inside ∷ p} {outside ∷ q} (zero , i∈p∩q) with x∈p∩q⁻ (inside ∷ p) (outside ∷ q) i∈p∩q
... | _ , ()
∣p─q∣<∣p∣ {suc n} {outside ∷ p} {outside ∷ q} (suc i , i∈p∩q) = ∣p─q∣<∣p∣ {n} {p} {q} (i , drop-there i∈p∩q)
∣p─q∣<∣p∣ {suc n} {outside ∷ p} {inside ∷ q} (suc i , i∈p∩q) = ∣p─q∣<∣p∣ {n} {p} {q} (i , drop-there i∈p∩q)
∣p─q∣<∣p∣ {suc n} {inside ∷ p} {outside ∷ q} (suc i , i∈p∩q) = s≤s (∣p─q∣<∣p∣ {n} {p} {q} (i , drop-there i∈p∩q))
∣p─q∣<∣p∣ {suc n} {inside ∷ p} {inside ∷ q} (i , i∈p∩q) = s≤s (∣p─q∣≤∣p∣ p q)

∣p∪⁅i⁆∣≡1+∣p∣ : ∀ {n} {p : Subset n} {i : Fin n} → i ∉ p → ∣ p ∪ ⁅ i ⁆ ∣ ≡ suc ∣ p ∣
∣p∪⁅i⁆∣≡1+∣p∣ {_} {outside ∷ p} {zero}  i∉p = cong (λ q → suc ∣ q ∣) (∪-identityʳ p)
∣p∪⁅i⁆∣≡1+∣p∣ {_} {inside  ∷ p} {zero}  i∉p = contradiction here i∉p
∣p∪⁅i⁆∣≡1+∣p∣ {_} {outside ∷ p} {suc i} i∉p = ∣p∪⁅i⁆∣≡1+∣p∣ (i∉p ∘ there)
∣p∪⁅i⁆∣≡1+∣p∣ {_} {inside  ∷ p} {suc i} i∉p = cong suc (∣p∪⁅i⁆∣≡1+∣p∣ (i∉p ∘ there))

∣p-i∣<∣p∣ : ∀ {n} {p : Subset n} {i : Fin n} → i ∈ p → ∣ p - i ∣ < ∣ p ∣
∣p-i∣<∣p∣ {i = i} i∈p = ∣p─q∣<∣p∣ (i , x∈p∩q⁺ (i∈p , x∈⁅x⁆ i))

∣∁p∣≡n∸∣p∣ : ∀ {n} (p : Subset n) → ∣ ∁ p ∣ ≡ n ∸ ∣ p ∣
∣∁p∣≡n∸∣p∣ []            = refl
∣∁p∣≡n∸∣p∣ (inside  ∷ p) = ∣∁p∣≡n∸∣p∣ p
∣∁p∣≡n∸∣p∣ (outside ∷ p) = begin
  suc ∣ ∁ p ∣     ≡⟨ cong suc (∣∁p∣≡n∸∣p∣ p) ⟩
  suc (_ ∸ ∣ p ∣) ≡⟨ sym (+-∸-assoc 1 (∣p∣≤n p)) ⟩
  suc  _ ∸ ∣ p ∣  ∎
  where open ≡-Reasoning

x∈p∧x∉q⇒x∈p─q : x ∈ p → x ∉ q → x ∈ p ─ q
x∈p∧x∉q⇒x∈p─q {q = outside ∷ q} here        i∉q = here
x∈p∧x∉q⇒x∈p─q {q = inside  ∷ q} here        i∉q = contradiction here i∉q
x∈p∧x∉q⇒x∈p─q {q = outside ∷ q} (there i∈p) i∉q = there (x∈p∧x∉q⇒x∈p─q i∈p (i∉q ∘ there))
x∈p∧x∉q⇒x∈p─q {q = inside  ∷ q} (there i∈p) i∉q = there (x∈p∧x∉q⇒x∈p─q i∈p (i∉q ∘ there))

i∉p⇒i∉p─q : ∀ {n} {p : Subset n} {i} → i ∉ p → ∀ q → i ∉ p ─ q
i∉p⇒i∉p─q {0} {[]} {i} i∉p [] = ∉⊥
i∉p⇒i∉p─q {suc n} {outside ∷ p} {zero} i∉p (outside ∷ q) ()
i∉p⇒i∉p─q {suc n} {inside ∷ p} {zero} i∉p (x ∷ q) = contradiction here i∉p
i∉p⇒i∉p─q {suc n} {outside ∷ p} {zero} i∉p (inside ∷ q) ()
i∉p⇒i∉p─q {suc n} {x ∷ p} {suc i} i∉p (y ∷ q) with x∷p─y∷q≡z∷p─q p q x y
... | _ , ≡z∷p─q rewrite (sym ≡z∷p─q) = (i∉p⇒i∉p─q {p = p} {i} (i∉p ∘ there) q) ∘ drop-there

i∉p─q⇒i∉p : ∀ {n} {p q : Subset n} {i} → i ∉ p ─ q → i ∉ q → i ∉ p
i∉p─q⇒i∉p {0}     {[]} {[]} {i} i∉p─q i∉q = ∉⊥
i∉p─q⇒i∉p {suc n} {x ∷ p} {y ∷ q} {suc i} i∉x∷p─y∷q i∉q (there i∈p) =
  i∉p─q⇒i∉p i∉p─q (i∉q ∘ there) i∈p
  where
  i∉p─q : i ∉ (p ─ q)
  i∉p─q = i∉x∷p─y∷q ∘ (λ i∈p─q → subst (suc i ∈_)
    (proj₂ (x∷p─y∷q≡z∷p─q p q x y)) (there i∈p─q))
i∉p─q⇒i∉p {.(suc _)} {inside ∷ p} {outside ∷ q} {zero} i∉p─q i∉q here = i∉p─q here
i∉p─q⇒i∉p {.(suc _)} {inside ∷ p} {inside ∷ q} {zero} i∉p─q i∉q here = i∉q here

p─q─r≡p─q∪r : ∀ (p q r : Subset n) → (p ─ q) ─ r ≡ p ─ (q ∪ r)
p─q─r≡p─q∪r []            q r = refl
p─q─r≡p─q∪r (outside ∷ p) (outside ∷ q) (outside ∷ r) = cong (_ ∷_) (p─q─r≡p─q∪r p q r)
p─q─r≡p─q∪r (outside ∷ p) (outside ∷ q) (inside  ∷ r) = cong (_ ∷_) (p─q─r≡p─q∪r p q r)
p─q─r≡p─q∪r (outside ∷ p) (inside  ∷ q) (outside ∷ r) = cong (_ ∷_) (p─q─r≡p─q∪r p q r)
p─q─r≡p─q∪r (outside ∷ p) (inside  ∷ q) (inside  ∷ r) = cong (_ ∷_) (p─q─r≡p─q∪r p q r)
p─q─r≡p─q∪r (inside  ∷ p) (outside ∷ q) (outside ∷ r) = cong (_ ∷_) (p─q─r≡p─q∪r p q r)
p─q─r≡p─q∪r (inside  ∷ p) (outside ∷ q) (inside  ∷ r) = cong (_ ∷_) (p─q─r≡p─q∪r p q r)
p─q─r≡p─q∪r (inside  ∷ p) (inside  ∷ q) (outside ∷ r) = cong (_ ∷_) (p─q─r≡p─q∪r p q r)
p─q─r≡p─q∪r (inside  ∷ p) (inside  ∷ q) (inside  ∷ r) = cong (_ ∷_) (p─q─r≡p─q∪r p q r)

p─q─r≡p─r─q : ∀ (p q r : Subset n) → (p ─ q) ─ r ≡ (p ─ r) ─ q
p─q─r≡p─r─q p q r = begin
  (p ─ q) ─ r ≡⟨ p─q─r≡p─q∪r p q r ⟩
  p ─ (q ∪ r) ≡⟨ cong (p ─_) (∪-comm q r) ⟩
  p ─ (r ∪ q) ≡⟨ sym (p─q─r≡p─q∪r p r q) ⟩
  (p ─ r) ─ q ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- -_

x∈p∧x≢y⇒x∈p-y : x ∈ p → x ≢ y → x ∈ p - y
x∈p∧x≢y⇒x∈p-y x∈p x≢y = x∈p∧x∉q⇒x∈p─q x∈p (i∉⁅j⁆ x≢y)

p─x─y≡p─y─x : ∀ (p : Subset n) x y → (p - x) - y ≡ (p - y) - x
p─x─y≡p─y─x p x y = p─q─r≡p─r─q p ⁅ x ⁆ ⁅ y ⁆
