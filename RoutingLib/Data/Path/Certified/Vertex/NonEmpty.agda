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

module RoutingLib.Data.VertexPath.NonEmpty where

  ------------------------------------------------------------------------------
  -- Datatypes

  Arc : Set
  Arc = ℕ × ℕ

  mutual

    infix 4 _∈_ _∉_

    data Pathⁿᵗ : Set where
      [_]   : (i : ℕ) → Pathⁿᵗ
      _∷_∣_ : (i : ℕ) (p : Pathⁿᵗ) → i ∉ p → Pathⁿᵗ

    data _∉_ : ℕ → Pathⁿᵗ → Set where
      notThere : ∀ {k i} → k ≢ i → k ∉ [ i ]
      notHere  : ∀ {k i p i∉p} → k ≢ i → k ∉ p → k ∉ i ∷ p ∣ i∉p

  _∈_ : ℕ → Pathⁿᵗ → Set
  i ∈ p = ¬ (i ∉ p)

  ------------------------------------------------------------------------------
  -- Operations

  length : Pathⁿᵗ → ℕ
  length [ _ ]       = 1
  length (_ ∷ p ∣ _) = suc (length p)

  -- Orders
{-
  -- Length order
  infix 4  _≤ₗ_
  _≤ₗ_ : ∀ {n} → Rel (Pathⁿᵗ n) ℓ₀
  p ≤ₗ q = length p ≤ℕ length q
-}
