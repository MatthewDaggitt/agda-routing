-- imports
open import Data.Nat
  using (ℕ; zero; suc)
open import Data.Fin
  using (Fin)
open import NatInf
open import NatInf.Properties
open import Data.Product
  using (∃; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl)
open import Data.Fin.Dec
  using (all?; ¬∀⟶∃¬)
open import Relation.Nullary
  using (¬_; yes; no)
open import Relation.Nullary.Negation
  using (contradiction)
open import Relation.Binary
  using (Reflexive; Antisymmetric; Transitive; Symmetric; IsPreorder; _⇒_)
open import Functions.Properties
  using (min∞-equiv)

module AllPairs.Properties (n : ℕ) where

  open import AllPairs n

  path-cost-monotone : ∀ {g g'} → (∀ i j → g i j ≤ g' i j) →
                       (∀ i j k → path-cost g i j k ≤ path-cost g' i j k)
  path-cost-monotone g≤g' i j k = +-mono-≤ (g≤g' i k) (g≤g' k j)

  path-cost-equiv : ∀ {g g'} → (∀ i j → g i j ≡ g' i j) →
                    ∀ i j k → path-cost g i j k ≡ path-cost g' i j k
  path-cost-equiv g≡g' i j k = +-mono (g≡g' i k) (g≡g' k j)

  ≼-refl : ∀ i → Reflexive [ i ]_≼_
  ≼-refl _ i = ≤-refl

  ≼-reflexive : ∀ i → _≡ᵣ_ ⇒ [ i ]_≼_
  ≼-reflexive i x≡y = λ j → ≤-reflexive (x≡y j)

  ≼-antisym : ∀ i → Antisymmetric _≡ᵣ_ [ i ]_≼_
  ≼-antisym _ {x} {y} x≼y y≼x = λ i → (≤-antisym (x≼y i) (y≼x i))

  ≼-trans : ∀ i → Transitive [ i ]_≼_
  ≼-trans _ x≼y y≼z = λ i → ≤-trans (x≼y i) (y≼z i)

  reflₘ : Reflexive _≡ₘ_
  reflₘ i j = refl

  symₘ : Symmetric _≡ₘ_
  symₘ g≡h i = symᵣ (g≡h i)

  transₘ : Transitive _≡ₘ_
  transₘ x≡y y≡z i = transᵣ (x≡y i) (y≡z i)

  congₘ : ∀ {x y} → x ≡ₘ y → f x ≡ₘ f y
  congₘ {x} {y} x≡y i j = min∞-equiv (path-cost-equiv x≡y i j)

  ≡ᵣ⇒≼ : ∀ {x y} i → x ≡ᵣ y → [ i ] x ≼ y
  ≡ᵣ⇒≼ i x = λ j → ≤-reflexive (x j)

  isPreorder : IsPreorder _≡ₘ_ _≼ₘ_
  isPreorder = record {
    isEquivalence = record {
      refl = reflₘ ;
      sym = symₘ ;
      trans = transₘ
      } ;
    reflexive = λ x i → ≡ᵣ⇒≼ i (x i) ;
    trans = λ x≼y y≼z i → ≼-trans i (x≼y i) (y≼z i)
    }

  ≢ᵣ-witness : ∀ {x y : Fin n → ℕ∞} → x ≢ᵣ y → ∃ λ i → x i ≢ y i
  ≢ᵣ-witness {x} {y} x≢y with all? (λ i → x i ≟ y i)
  ... | yes all = contradiction all x≢y
  ... | no ¬all =  ¬∀⟶∃¬ n (λ i → x i ≡ y i) (λ i → x i ≟ y i) ¬all

  ≢ᵣ-from-witness : ∀ {x y} → (∃ λ i → x i ≢ y i) → x ≢ᵣ y
  ≢ᵣ-from-witness {x} {y} (i , x≢y) with x ≟ᵣ y
  ... | yes p = contradiction (p i) x≢y
  ... | no ¬p = ¬p

  ≢ₘ-witness : ∀ {g h : Fin n → Fin n → ℕ∞} → g ≢ₘ h → ∃ λ i → ∃ λ j → g i j ≢ h i j
  ≢ₘ-witness {g} {h} g≢h with all? (λ i → g i ≟ᵣ h i)
  ... | yes all = contradiction all g≢h
  ... | no ¬all with ¬∀⟶∃¬ n (λ i → g i ≡ᵣ h i) (λ i → g i ≟ᵣ h i) ¬all
  ... | i , gᵢ≢hᵢ = i , ≢ᵣ-witness gᵢ≢hᵢ
  
