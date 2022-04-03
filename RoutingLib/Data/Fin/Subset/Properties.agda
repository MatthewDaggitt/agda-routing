open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s; _⊔_; _⊓_; _∸_)
open import Data.Nat.Properties hiding (_≟_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (¬∀⟶∃¬)
open import Data.Fin.Subset
open import Data.Fin.Subset.Properties
open import Data.Bool using (_≟_)
open import Data.Product using (∃; _,_; _×_; proj₂)
open import Data.Sum using ([_,_]′; inj₁; inj₂)
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
-- ⊤

⊤-full : ∀ {n} → Full {n} ⊤
⊤-full zero    = here
⊤-full (suc i) = there (⊤-full i)

∣p∣<n⇒Nonfull : ∀ {p : Subset n} → ∣ p ∣ < n → Nonfull p
∣p∣<n⇒Nonfull {p = []}          ()
∣p∣<n⇒Nonfull {p = outside ∷ p} |p|<n       full = contradiction (full zero) λ()
∣p∣<n⇒Nonfull {p = inside  ∷ p} (s≤s |p|<n) full = ∣p∣<n⇒Nonfull |p|<n (drop-there ∘ full ∘ suc)

Nonfull-witness : ∀ {p : Subset n} → Nonfull p → ∃ λ i → i ∉ p
Nonfull-witness {n = n} {p} ¬pᶠ = ¬∀⟶∃¬ n (_∈ p) (_∈? p) ¬pᶠ

------------------------------------------------------------------------
-- ⁅_⁆

Nonfull⁅i⁆ : ∀ (i : Fin (suc (suc n))) → Nonfull ⁅ i ⁆
Nonfull⁅i⁆ zero    full = ∉⊥ (drop-there (full (suc zero)))
Nonfull⁅i⁆ (suc i) full = contradiction (full zero) λ()

Nonfull⁅i⁆′ : 1 < n → (i : Fin n) → Nonfull ⁅ i ⁆
Nonfull⁅i⁆′ (s≤s (s≤s _)) zero    full = ∉⊥ (drop-there (full (suc zero)))
Nonfull⁅i⁆′ (s≤s (s≤s _)) (suc i) full = contradiction  (full zero) λ()

------------------------------------------------------------------------
-- Complement

p∩∁p≡⊥ : ∀ (p : Subset n) → p ∩ ∁ p ≡ ⊥
p∩∁p≡⊥ []            = refl
p∩∁p≡⊥ (outside ∷ p) = cong (outside ∷_) (p∩∁p≡⊥ p)
p∩∁p≡⊥ (inside  ∷ p) = cong (outside ∷_) (p∩∁p≡⊥ p)

∁⊤≡⊥ : ∀ {n} → ∁ ⊤ ≡ ⊥ {n}
∁⊤≡⊥ {zero}  = refl
∁⊤≡⊥ {suc n} = cong (_ ∷_) ∁⊤≡⊥

------------------------------------------------------------------------
-- Membership

∉-contract : x ∉ p → ∀ {y} → suc x ∉ y ∷ p
∉-contract ∉p (there ∈p) = ∉p ∈p

------------------------------------------------------------------------
-- Union

x∉p∪q⁺ :  x ∉ p → x ∉ q → x ∉ p ∪ q
x∉p∪q⁺ x∉p x∉q = [ x∉p , x∉q ]′ ∘ x∈p∪q⁻ _ _

x∉p∪q⁻ :  ∀ x (p q : Subset n) → x ∉ p ∪ q → x ∉ p × x ∉ q
x∉p∪q⁻ _ _ _ x∉p∪q = x∉p∪q ∘ x∈p∪q⁺ ∘ inj₁ , x∉p∪q ∘ x∈p∪q⁺ ∘ inj₂

∣p∪⁅i⁆∣≡1+∣p∣ : ∀ {i : Fin n} → i ∉ p → ∣ p ∪ ⁅ i ⁆ ∣ ≡ suc ∣ p ∣
∣p∪⁅i⁆∣≡1+∣p∣ {_} {outside ∷ p} {zero}  i∉p = cong (suc ∘ ∣_∣) (∪-identityʳ p)
∣p∪⁅i⁆∣≡1+∣p∣ {_} {inside  ∷ p} {zero}  i∉p = contradiction here i∉p
∣p∪⁅i⁆∣≡1+∣p∣ {_} {outside ∷ p} {suc i} i∉p = ∣p∪⁅i⁆∣≡1+∣p∣ (i∉p ∘ there)
∣p∪⁅i⁆∣≡1+∣p∣ {_} {inside  ∷ p} {suc i} i∉p = cong suc (∣p∪⁅i⁆∣≡1+∣p∣ (i∉p ∘ there))

------------------------------------------------------------------------
-- Difference

x∷p─y∷q≡z∷p─q : ∀ (p q : Subset n) x y → ∃ λ z → z ∷ (p ─ q) ≡ (x ∷ p) ─ (y ∷ q)
x∷p─y∷q≡z∷p─q p q x outside = x       , refl
x∷p─y∷q≡z∷p─q p q x inside  = outside , refl

i∉p⇒i∉p─q : ∀ {i} → i ∉ p → ∀ q → i ∉ p ─ q
i∉p⇒i∉p─q {0} {[]} {i} i∉p [] = ∉⊥
i∉p⇒i∉p─q {suc n} {outside ∷ p} {zero} i∉p (outside ∷ q) ()
i∉p⇒i∉p─q {suc n} {inside ∷ p} {zero} i∉p (x ∷ q) = contradiction here i∉p
i∉p⇒i∉p─q {suc n} {outside ∷ p} {zero} i∉p (inside ∷ q) ()
i∉p⇒i∉p─q {suc n} {x ∷ p} {suc i} i∉p (y ∷ q) with x∷p─y∷q≡z∷p─q p q x y
... | _ , ≡z∷p─q rewrite (sym ≡z∷p─q) = (i∉p⇒i∉p─q {p = p} {i} (i∉p ∘ there) q) ∘ drop-there

i∉p─q⇒i∉p : ∀ {i} → i ∉ p ─ q → i ∉ q → i ∉ p
i∉p─q⇒i∉p {_} {[]}    {[]}    {i} i∉p─q i∉q = ∉⊥
i∉p─q⇒i∉p {_} {x ∷ p} {y ∷ q} {suc i} i∉x∷p─y∷q i∉q (there i∈p) =
  i∉p─q⇒i∉p i∉p─q (i∉q ∘ there) i∈p
  where
  i∉p─q : i ∉ (p ─ q)
  i∉p─q = i∉x∷p─y∷q ∘ (λ i∈p─q → subst (suc i ∈_)
    (proj₂ (x∷p─y∷q≡z∷p─q p q x y)) (there i∈p─q))
i∉p─q⇒i∉p {_} {inside ∷ p} {outside ∷ q} {zero} i∉p─q i∉q here = i∉p─q here
i∉p─q⇒i∉p {_} {inside ∷ p} {inside ∷ q} {zero} i∉p─q i∉q here = i∉q here
