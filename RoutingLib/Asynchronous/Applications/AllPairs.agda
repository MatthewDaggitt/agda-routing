open import Data.Fin using (Fin)
open import Data.Fin.Dec using (all?;  ¬∀⟶∃¬)
open import Data.Nat using (ℕ)
open import Level using () renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Setoid; Rel; Reflexive; Symmetric; Transitive; Decidable; _⇒_; IsEquivalence; IsDecEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; _≢_)
open import Relation.Nullary using (¬_; yes; no)

open import RoutingLib.Asynchronous using (Parallelisation)
open import RoutingLib.Data.NatInf
open import RoutingLib.Data.Table using (Table; min∞)
open import RoutingLib.Data.Table.All using (All)

module RoutingLib.Asynchronous.Applications.AllPairs (n : ℕ) where
  -- Row type - Table of ℕ∞
  Row : Set
  Row = Table ℕ∞ n

  -- Matrix type - Table of Row
  Matrix : Set
  Matrix = Table Row n

  -- Equality over Row
  _≡ᵣ_ : Rel Row lzero
  x ≡ᵣ y = ∀ i → x i ≡ y i

  _≢ᵣ_ : Rel Row lzero
  x ≢ᵣ y = ¬ (x ≡ᵣ y)

  -- Properties of Equality over Row
  reflexiveᵣ : _≡_ ⇒ _≡ᵣ_
  reflexiveᵣ refl i = refl

  reflᵣ : Reflexive _≡ᵣ_
  reflᵣ i = refl

  symᵣ : Symmetric _≡ᵣ_
  symᵣ x≡y i = sym (x≡y i)

  transᵣ : Transitive _≡ᵣ_
  transᵣ x≡y y≡z i = trans (x≡y i) (y≡z i)

  -- Decidablility of Row Equality
  _≟ᵣ_ : Decidable _≡ᵣ_
  x ≟ᵣ y = all? (λ i → (x i) ≟ (y i))

  -- Row Ordering Relation
  _≼_ : Rel Row lzero
  x ≼ y = ∀ i → x i ≤ y i

  -- Matrix Equality
  _≡ₘ_ : Rel Matrix lzero
  g ≡ₘ h = ∀ i → g i ≡ᵣ h i

  _≢ₘ_ : Rel Matrix lzero
  g ≢ₘ h = ¬ (g ≡ₘ h)

  -- Decidability of Matrix Equality
  _≟ₘ_ : Decidable _≡ₘ_
  g ≟ₘ h = all? (λ i → (g i) ≟ᵣ (h i))

  -- Matrix Ordering Relation
  _≼ₘ_ : Rel Matrix lzero
  g ≼ₘ h = ∀ i → g i ≼ h i

  -- Equality over Row is an equivalence class
  isEquivalenceᵣ : IsEquivalence _≡ᵣ_
  isEquivalenceᵣ = record {
    refl  = reflᵣ ;
    sym   = symᵣ ;
    trans = transᵣ
    }

  -- Equality over Row is a decidable equivalence class
  isDecEquivalence : IsDecEquivalence _≡ᵣ_
  isDecEquivalence = record {
    isEquivalence = isEquivalenceᵣ ;
    _≟_           = _≟ᵣ_
    }

  -- Row Setoid
  row : Setoid lzero lzero
  row = record {
    Carrier = Row ;
    _≈_ = _≡ᵣ_ ;
    isEquivalence = isEquivalenceᵣ
    }

  -- Cost of going from node i to j through k
  path-cost : Matrix → (i j k : Fin n) → ℕ∞
  path-cost g i j k = (g i k) + (g k j) 

  -- Shortest cost from node i to j in matrix
  f : Matrix → Fin n → Row
  f g i j = min∞ (g i j) (path-cost g i j)

  matrix : Fin n → Setoid lzero lzero
  matrix _ = row

  all-pairs-parallelisation : Parallelisation matrix
  all-pairs-parallelisation = record {f = f}
