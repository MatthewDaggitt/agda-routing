open import Data.Fin.Dec using (all?; ¬∀⟶∃¬)
open import Data.Nat using (ℕ)
open import Data.Product using (∃; _,_)
open import Relation.Binary using (Reflexive; Antisymmetric; Transitive; Symmetric; IsPreorder; _⇒_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.NatInf
open import RoutingLib.Data.NatInf.Properties
open import RoutingLib.Data.Table.Properties using (min∞[s]≡min∞[t])

module RoutingLib.Asynchronous.Applications.AllPairs.Properties (n : ℕ) where

  open import RoutingLib.Asynchronous.Applications.AllPairs n
  
  path-cost-monotone : ∀ {g h} → g ≼ₘ h → ∀ i j k → path-cost g i j k ≤ path-cost h i j k
  path-cost-monotone g≼ₘh i j k = +-mono-≤ (g≼ₘh i k) (g≼ₘh k j)

  path-cost-equiv : ∀ {g h} → g ≡ₘ h → ∀ i j k → path-cost g i j k ≡ path-cost h i j k
  path-cost-equiv g≡ₘh i j k = +-mono (g≡ₘh i k) (g≡ₘh k j)

  ≼-refl : Reflexive _≼_
  ≼-refl i = ≤-refl

  ≼-reflexive :  _≡ᵣ_ ⇒ _≼_
  ≼-reflexive x≡y i = ≤-reflexive (x≡y i)

  ≼-antisym : Antisymmetric _≡ᵣ_ _≼_
  ≼-antisym x≼y y≼x i = ≤-antisym (x≼y i) (y≼x i)

  ≼-trans : Transitive _≼_
  ≼-trans x≼y y≼z i = ≤-trans (x≼y i) (y≼z i)

  reflₘ : Reflexive _≡ₘ_
  reflₘ i j = refl

  symₘ : Symmetric _≡ₘ_
  symₘ g≡h i = symᵣ (g≡h i)

  transₘ : Transitive _≡ₘ_
  transₘ x≡y y≡z i = transᵣ (x≡y i) (y≡z i)

  f-cong : ∀ {x y} → x ≡ₘ y → f x ≡ₘ f y
  f-cong {x} {y} x≡y i j = min∞[s]≡min∞[t] (x≡y i j) (path-cost-equiv x≡y i j)
  
  ≡ᵣ⇒≼ : ∀ {x y} → x ≡ᵣ y → x ≼ y
  ≡ᵣ⇒≼ x≡y i = ≤-reflexive (x≡y i)

  isPreorder : IsPreorder _≡ₘ_ _≼ₘ_
  isPreorder = record {
    isEquivalence = record {
      refl = reflₘ ;
      sym = symₘ ;
      trans = transₘ
      } ;
    reflexive = λ x i → ≡ᵣ⇒≼ (x i) ;
    trans = λ x≼y y≼z i → ≼-trans (x≼y i) (y≼z i)
    }

  ≢ᵣ-witness : ∀ {x y} → x ≢ᵣ y → ∃ λ i → x i ≢ y i
  ≢ᵣ-witness {x} {y} x≢y with all? (λ i → x i ≟ y i)
  ... | yes all = contradiction all x≢y
  ... | no ¬all =  ¬∀⟶∃¬ n (λ i → x i ≡ y i) (λ i → x i ≟ y i) ¬all

  ≢ᵣ-from-witness : ∀ {x y} → (∃ λ i → x i ≢ y i) → x ≢ᵣ y
  ≢ᵣ-from-witness {x} {y} (i , x≢y) with x ≟ᵣ y
  ... | yes p = contradiction (p i) x≢y
  ... | no ¬p = ¬p

  ≢ₘ-witness-≢ᵣ : ∀ {g h} → g ≢ₘ h → ∃ λ i → g i ≢ᵣ h i
  ≢ₘ-witness-≢ᵣ {g} {h} g≢h with all? (λ i → g i ≟ᵣ h i)
  ... | yes all = contradiction all g≢h
  ... | no ¬all = ¬∀⟶∃¬ n (λ i → g i ≡ᵣ h i) (λ i → g i ≟ᵣ h i) ¬all

  ≢ₘ-witness : ∀ {g h} → g ≢ₘ h → ∃ λ i → ∃ λ j → g i j ≢ h i j
  ≢ₘ-witness {g} {h} g≢h with ≢ₘ-witness-≢ᵣ g≢h
  ... | i , gᵢ≢hᵢ = i , ≢ᵣ-witness gᵢ≢hᵢ
