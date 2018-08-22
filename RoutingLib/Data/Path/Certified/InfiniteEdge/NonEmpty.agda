open import Data.Fin using (Fin; zero; suc; _<_; _≤_; toℕ)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; map)
open import Level using () renaming (zero to ℓ₀)
open import Relation.Nullary using (¬_)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Unary using (Pred; Decidable)

module RoutingLib.Data.Path.EdgePath.NonEmpty where

  ------------------------------------------------------------------------------
  -- Datatypes

  Edge : Set
  Edge = ℕ × ℕ

  mutual

    infix 4 _∈_ _∉_ _⇿_

    data Pathⁿᵗ : Set where
      []      : Pathⁿᵗ
      _∷_∣_∣_ : ∀ e p (e⇿p : e ⇿ p) (e∉p : proj₁ e ∉ p) → Pathⁿᵗ

    data _⇿_ : Edge → Pathⁿᵗ → Set where
      start     : ∀ {i j}              → i ≢ j → (i , j) ⇿ []
      continue  : ∀ {i j k p jk⇿p j∉p} → i ≢ j → (i , j) ⇿ (j , k) ∷ p ∣ jk⇿p ∣ j∉p

    data _∉_ : ℕ → Pathⁿᵗ → Set where
      notThere : ∀ {k}                → k ∉ []
      notHere  : ∀ {i j k p ij⇿p i∉p} → k ≢ i → k ≢ j → k ∉ p → k ∉ (i , j) ∷ p ∣ ij⇿p ∣ i∉p

  _∈_ : ℕ → Pathⁿᵗ → Set
  i ∈ p = ¬ (i ∉ p)

  ------------------------------------------------------------------------------
  -- Operations

  length : Pathⁿᵗ → ℕ
  length []              = 0
  length (_ ∷ p ∣ _ ∣ _) = suc (length p)



  
  postulate count : ∀ {p} {P : Pred ℕ p} → Decidable P → Pathⁿᵗ → ℕ
