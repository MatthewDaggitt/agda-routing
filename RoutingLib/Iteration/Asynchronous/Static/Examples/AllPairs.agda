open import Data.Fin using (Fin)
open import Data.Fin.Dec using (all?;  ¬∀⟶∃¬)
open import Data.Nat using (ℕ)
open import Level using (0ℓ)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; _≢_)
open import Relation.Binary.Indexed.Homogeneous using (IndexedSetoid)
open import Relation.Nullary using (¬_; yes; no)

open import RoutingLib.Data.NatInf
open import RoutingLib.Data.Table using (Table; min∞)
open import RoutingLib.Data.Table.All using (All)
open import RoutingLib.Relation.Binary.Indexed.Homogeneous
  using (triviallyIndexSetoid)

open import RoutingLib.Iteration.Asynchronous.Static

module RoutingLib.Iteration.Asynchronous.Static.Examples.AllPairs (n : ℕ) where

  -- Row type - Table of ℕ∞
  Row : Set
  Row = Table ℕ∞ n

  -- Matrix type - Table of Row
  Matrix : Set
  Matrix = Table Row n

  -- Equality over Row
  _≡ᵣ_ : Rel Row 0ℓ
  x ≡ᵣ y = ∀ i → x i ≡ y i

  _≢ᵣ_ : Rel Row 0ℓ
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
  _≼_ : Rel Row 0ℓ
  x ≼ y = ∀ i → x i ≤ y i

  -- Matrix Equality
  _≡ₘ_ : Rel Matrix 0ℓ
  g ≡ₘ h = ∀ i → g i ≡ᵣ h i

  _≢ₘ_ : Rel Matrix 0ℓ
  g ≢ₘ h = ¬ (g ≡ₘ h)

  -- Decidability of Matrix Equality
  _≟ₘ_ : Decidable _≡ₘ_
  g ≟ₘ h = all? (λ i → (g i) ≟ᵣ (h i))

  -- Matrix Ordering Relation
  _≼ₘ_ : Rel Matrix 0ℓ
  g ≼ₘ h = ∀ i → g i ≼ h i

  -- Equality over Row is an equivalence class
  isEquivalenceᵣ : IsEquivalence _≡ᵣ_
  isEquivalenceᵣ = record
    { refl  = reflᵣ
    ; sym   = symᵣ
    ; trans = transᵣ
    }

  -- Equality over Row is a decidable equivalence class
  isDecEquivalence : IsDecEquivalence _≡ᵣ_
  isDecEquivalence = record
    { isEquivalence = isEquivalenceᵣ
    ; _≟_           = _≟ᵣ_
    }

  -- Row Setoid
  row : Setoid 0ℓ 0ℓ
  row = record
    { isEquivalence = isEquivalenceᵣ
    }

  -- Cost of going from node i to j through k
  path-cost : Matrix → (i j k : Fin n) → ℕ∞
  path-cost X i j k = (X i k) + (X k j)

  -- Shortest cost from node i to j in matrix
  F : Matrix → Fin n → Row
  F X i j = min∞ (X i j) (path-cost X i j)

  F-cong : F Preserves _≡ₘ_ ⟶ _≡ₘ_
  F-cong = {!!}
  
  matrix : IndexedSetoid (Fin n) 0ℓ 0ℓ
  matrix = triviallyIndexSetoid (Fin n) row

  allPairs-isAsyncIterable : IsAsyncIterable _≡ᵣ_ F
  allPairs-isAsyncIterable = record
    { isDecEquivalenceᵢ = {!!}
    ; F-cong           = F-cong
    }

  allPairs∥ : AsyncIterable 0ℓ 0ℓ n
  allPairs∥ = record
    { isAsyncIterable = allPairs-isAsyncIterable
    }
