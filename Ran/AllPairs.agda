-- imports
open import Data.Nat
  using (ℕ; zero; suc)
open import Relation.Binary
  using (Setoid; Rel; Reflexive; Symmetric; Transitive; Substitutive; Decidable;
    IsEquivalence; IsDecEquivalence; Sym; Antisymmetric; _⇒_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst; _≢_)
open import Level
  using () renaming (zero to lzero; suc to lsuc)
open import Data.Fin
  using (Fin) renaming (zero to fzero; suc to fsuc)
open import Function
  using (flip)
open import Computation
  using (Computation; ACO)
open import Functions
  using (min∞)
open import Functions.Properties
  using (min∞-monotone)
open import NatInf
  using (ℕ∞; _+_; _≤_; _≟_)
open import Data.Product
  using (_×_; _,_)
open import Relation.Unary
  using (Pred; U; U-Universal)
open import Data.Fin.Dec
  using (all?;  ¬∀⟶∃¬)
open import Relation.Nullary
  using (yes; no; ¬_)
open import Data.Product
  using (∃)
open import Relation.Nullary.Negation
  using (contradiction)

open Setoid
  using (Carrier; _≈_; isEquivalence)

module AllPairs (n : ℕ) where

  _≡ᵣ_ : Rel (Fin n → ℕ∞) lzero
  x ≡ᵣ y = ∀ i → x i ≡ y i

  _≢ᵣ_ : Rel (Fin n → ℕ∞) lzero
  x ≢ᵣ y = ¬ (x ≡ᵣ y)

  reflexive : _≡_ ⇒ _≡ᵣ_
  reflexive refl i = refl

  reflᵣ : Reflexive _≡ᵣ_
  reflᵣ i = refl

  symᵣ : Symmetric _≡ᵣ_
  symᵣ x≡y i = sym (x≡y i)

  transᵣ : Transitive _≡ᵣ_
  transᵣ x≡y y≡z i = trans (x≡y i) (y≡z i)

  _≟ᵣ_ : Decidable _≡ᵣ_
  x ≟ᵣ y = all? (λ i → (x i) ≟ (y i))

  [_]_≼_ : Fin n → Rel (Fin n → ℕ∞) lzero
  [ _ ] x ≼ y = ∀ i → x i ≤ y i

  _≡ₘ_ : Rel (Fin n → Fin n → ℕ∞) lzero
  g ≡ₘ h = ∀ i → g i ≡ᵣ h i

  _≢ₘ_ : Rel (Fin n → Fin n → ℕ∞) lzero
  g ≢ₘ h = ¬ (g ≡ₘ h)

  _≟ₘ_ : Decidable _≡ₘ_
  g ≟ₘ h = all? (λ i → (g i) ≟ᵣ (h i))
  
  _≼ₘ_ : Rel (Fin n → Fin n → ℕ∞) lzero
  g ≼ₘ h = ∀ i → [ i ] g i ≼ h i

  isEquivalenceᵣ : IsEquivalence _≡ᵣ_
  isEquivalenceᵣ = record {
    refl  = reflᵣ ;
    sym   = symᵣ ;
    trans = transᵣ
    }

  isDecEquivalence : IsDecEquivalence _≡ᵣ_
  isDecEquivalence = record {
    isEquivalence = isEquivalenceᵣ ;
    _≟_           = _≟ᵣ_
    }

  row : Setoid lzero lzero
  row = record {
    Carrier = Fin n → ℕ∞ ;
    _≈_ = _≡ᵣ_ ;
    isEquivalence = isEquivalenceᵣ
    }

  grid : Fin n → Setoid lzero lzero
  grid i = row

  -- Calculate path from i to j stopping at k
  path-cost : (Fin n → Fin n → ℕ∞) → (i j k : Fin n) → ℕ∞
  path-cost g i j k = (g i k) + (g k j) 

  f : (Fin n → Fin n → ℕ∞) → Fin n → (Fin n → ℕ∞)
  f g i j = min∞ (path-cost g i j)

  -- postulate subst-f : ∀ {x y} f → x ≡ᵣ y → {!!} 


  all-pairs-comp : Computation grid
  all-pairs-comp = record {
    f = f
    }
