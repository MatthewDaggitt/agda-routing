open import Data.Nat using (suc; _≤_; _<_; s≤s)
open import Data.Product using (_,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (yes; no)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; inspect; [_]; refl; sym)
open import Relation.Unary using (Decidable)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Path.Certified.FiniteEdge
open import RoutingLib.Data.Path.Certified.FiniteEdge.Properties hiding (_⇿?_; _∉?_)
open import RoutingLib.Data.Path.Certified.FiniteEdge.NonEmpty.Properties using (_⇿?_; _∉?_)

open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra as RoutingAlgebraProperties

module RoutingLib.Routing.Algebra.Properties.PathAlgebra
  {a b ℓ n} (algebra : PathAlgebra a b ℓ n) where

open PathAlgebra algebra
open EqReasoning S

--------------------------------------------------------------------------------
-- Import routing algebra properties

open RoutingAlgebraProperties routingAlgebra public

--------------------------------------------------------------------------------
-- Path properties

abstract

  p[∞]≈∅ : path ∞ ≈ₚ invalid
  p[∞]≈∅ = r≈∞⇒path[r]≈∅ ≈-refl

  p[0]≈[] : path 0# ≈ₚ valid []
  p[0]≈[] = r≈0⇒path[r]≈[] ≈-refl

  p[r]≡∅⇒Aᵢⱼr≈∞ : ∀ {i j r} → path r ≡ invalid → A i j ▷ r ≈ ∞
  p[r]≡∅⇒Aᵢⱼr≈∞ {i} {j} {r} pᵣ≡∅ = begin
    A i j ▷ r ≈⟨ ▷-cong (A i j) (path[r]≈∅⇒r≈∞ (≈ₚ-reflexive pᵣ≡∅)) ⟩
    A i j ▷ ∞ ≈⟨ ▷-zero (A i j) ⟩
    ∞         ∎

--------------------------------------------------------------------------------
-- Weight properties

  weight-cong : ∀ {p q : Path n} → p ≈ₚ q → weight p ≈ weight q
  weight-cong invalid              = ≈-refl
  weight-cong (valid [])           = ≈-refl
  weight-cong (valid (refl ∷ p≈q)) = ▷-cong _ (weight-cong (valid p≈q))

--------------------------------------------------------------------------------
-- Consistency

  𝑪? : Decidable 𝑪
  𝑪? r = weight (path r) ≟ r

  𝑪-cong : ∀ {r s} → r ≈ s → 𝑪 r → 𝑪 s
  𝑪-cong r≈s rᶜ = ≈-trans (≈-trans (weight-cong (path-cong (≈-sym r≈s))) rᶜ) r≈s

  𝑰-cong : ∀ {r s} → r ≈ s → 𝑰 r → 𝑰 s
  𝑰-cong r≈s rⁱ sᶜ = rⁱ (𝑪-cong (≈-sym r≈s) sᶜ)

  𝑪𝑰⇒≉ : ∀ {r s} → 𝑪 r → 𝑰 s → r ≉ s
  𝑪𝑰⇒≉ rᶜ sⁱ r≈s = sⁱ (𝑪-cong r≈s rᶜ)

  0ᶜ : 𝑪 0#
  0ᶜ = weight-cong p[0]≈[]

  ∞ᶜ : 𝑪 ∞
  ∞ᶜ = weight-cong p[∞]≈∅

  ⊕-pres-𝑪 : ∀ {r s} → 𝑪 r → 𝑪 s → 𝑪 (r ⊕ s)
  ⊕-pres-𝑪 {r} {s} rᶜ sᶜ with ⊕-sel r s
  ... | inj₁ r⊕s≈r = 𝑪-cong (≈-sym r⊕s≈r) rᶜ
  ... | inj₂ r⊕s≈s = 𝑪-cong (≈-sym r⊕s≈s) sᶜ

  ▷-pres-𝑪 : ∀ i j {r} → 𝑪 r → 𝑪 (A i j ▷ r)
  ▷-pres-𝑪 i j {r} rᶜ with A i j ▷ r ≟ ∞
  ... | yes Aᵢⱼ▷r≈∞ = 𝑪-cong (≈-sym Aᵢⱼ▷r≈∞) ∞ᶜ
  ... | no  Aᵢⱼ▷r≉∞ with path r | inspect path r
  ...   | invalid | [ pᵣ≡∅ ] = contradiction (p[r]≡∅⇒Aᵢⱼr≈∞ pᵣ≡∅) Aᵢⱼ▷r≉∞
  ...   | valid q | [ pᵣ≡q ] with ≈ₚ-reflexive pᵣ≡q | (i , j) ⇿? q | i ∉? q
  ...     | pᵣ≈q | no ¬ij⇿q | _       = 𝑪-cong (≈-sym (path-reject pᵣ≈q (inj₁ ¬ij⇿q))) ∞ᶜ
  ...     | pᵣ≈q | _        | no  i∈q = 𝑪-cong (≈-sym (path-reject pᵣ≈q (inj₂ i∈q))) ∞ᶜ
  ...     | pᵣ≈q | yes ij⇿q | yes i∉q = begin
    weight (path (A i j ▷ r))                 ≈⟨ weight-cong (path-accept pᵣ≈q Aᵢⱼ▷r≉∞ ij⇿q i∉q) ⟩
    weight (valid ((i , j) ∷ q ∣ ij⇿q ∣ i∉q)) ≡⟨⟩
    A i j ▷ weight (valid q)                  ≈⟨ ▷-cong (A i j) rᶜ ⟩
    A i j ▷ r                                 ∎

  ▷-forces-𝑰 : ∀ {i j r} → 𝑰 (A i j ▷ r) → 𝑰 r
  ▷-forces-𝑰 Aᵢⱼrⁱ rᶜ = Aᵢⱼrⁱ (▷-pres-𝑪 _ _ rᶜ)

  weightᶜ : ∀ p → 𝑪 (weight p)
  weightᶜ invalid                            = ∞ᶜ
  weightᶜ (valid [])                         = 0ᶜ
  weightᶜ (valid ((i , j) ∷ p ∣ e⇿p ∣ e∉p)) with A i j ▷ weight (valid p) ≟ ∞
  ... | yes Aᵢⱼ▷wₚ≈∞ = 𝑪-cong (≈-sym Aᵢⱼ▷wₚ≈∞) ∞ᶜ
  ... | no  Aᵢⱼ▷wₚ≉∞ with path (weight (valid p)) | inspect path (weight (valid p))
  ...   | invalid | [ p[wₚ]≡∅ ] = 𝑪-cong (≈-sym (p[r]≡∅⇒Aᵢⱼr≈∞ p[wₚ]≡∅)) ∞ᶜ
  ...   | valid q | [ p[wₚ]≡q ] with ≈ₚ-reflexive p[wₚ]≡q | (i , j) ⇿? q | i ∉? q
  ...     | p[wₚ]≈q | no ¬ij⇿q | _       = 𝑪-cong (≈-sym (path-reject p[wₚ]≈q (inj₁ ¬ij⇿q))) ∞ᶜ
  ...     | p[wₚ]≈q | _        | no  i∈q = 𝑪-cong (≈-sym (path-reject p[wₚ]≈q (inj₂ i∈q))) ∞ᶜ
  ...     | p[wₚ]≈q | yes ij⇿q | yes i∉q = begin
    weight (path (A i j ▷ weight (valid p)))    ≈⟨ weight-cong (path-accept p[wₚ]≈q Aᵢⱼ▷wₚ≉∞ ij⇿q i∉q) ⟩
    weight (valid ((i , j) ∷ q ∣ ij⇿q ∣ i∉q))  ≡⟨⟩
    A i j ▷ weight (valid q)                    ≈⟨ ▷-cong (A i j) (weight-cong (≈ₚ-sym p[wₚ]≈q)) ⟩
    A i j ▷ weight (path (weight (valid p)))    ≈⟨ ▷-cong (A i j) (weightᶜ (valid p)) ⟩
    A i j ▷ weight (valid p)                    ∎

--------------------------------------------------------------------------------
-- Size properties

  size<n : 1 ≤ n → ∀ r → size r < n
  size<n (s≤s _) r = |p|<n (path _)

  size≤n+1 : ∀ r → size r ≤ suc n
  size≤n+1 r = |p|≤1+n (path r)

  size-cong : ∀ {r s} → r ≈ s → size r ≡ size s
  size-cong {r} {s} r≈s = length-cong (path-cong r≈s)

  size-incr : ∀ {i j r} → 𝑰 (A i j ▷ r) → suc (size r) ≡ size (A i j ▷ r)
  size-incr {i} {j} {r} Aᵢⱼ▷rⁱ with A i j ▷ r ≟ ∞
  ... | yes Aᵢⱼ▷r≈∞ = contradiction (𝑪-cong (≈-sym Aᵢⱼ▷r≈∞) ∞ᶜ) Aᵢⱼ▷rⁱ
  ... | no  Aᵢⱼ▷r≉∞ with path r | inspect path r
  ...   | invalid | [ pᵣ≡∅ ] = contradiction (p[r]≡∅⇒Aᵢⱼr≈∞ pᵣ≡∅) Aᵢⱼ▷r≉∞
  ...   | valid q | [ pᵣ≡q ] with ≈ₚ-reflexive pᵣ≡q | (i , j) ⇿? q | i ∉? q
  ...     | pᵣ≈q | no ¬ij⇿q | _       = contradiction (path-reject pᵣ≈q (inj₁ ¬ij⇿q)) Aᵢⱼ▷r≉∞
  ...     | pᵣ≈q | _        | no  i∈q = contradiction (path-reject pᵣ≈q (inj₂ i∈q)) Aᵢⱼ▷r≉∞
  ...     | pᵣ≈q | yes ij⇿q | yes i∉q = sym (length-cong (path-accept pᵣ≈q Aᵢⱼ▷r≉∞ ij⇿q i∉q))
