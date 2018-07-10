open import Data.Fin using (Fin; _<_; _≤_) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; map)
open import Level using () renaming (zero to ℓ₀)
open import Relation.Nullary using (¬_)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

module RoutingLib.Data.SimplePath.NonEmpty where

  ------------------------------------------------------------------------------
  -- Datatypes

  mutual

    infix 4 _∈_ _∉_ _⇿_

    data SimplePathⁿᵗ (n : ℕ) : Set where
      []      : SimplePathⁿᵗ n
      _∷_∣_∣_ : ∀ e p (e⇿p : e ⇿ p) (e∉p : proj₁ e ∉ p) → SimplePathⁿᵗ n

    data _⇿_ {n : ℕ} : Fin n × Fin n → SimplePathⁿᵗ n → Set where
      start     : ∀ {i j}              → i ≢ j → (i , j) ⇿ []
      continue  : ∀ {i j k p jk⇿p j∉p} → i ≢ j → (i , j) ⇿ (j , k) ∷ p ∣ jk⇿p ∣ j∉p

    data _∉_ {n : ℕ} : Fin n → SimplePathⁿᵗ n → Set where
      notThere : ∀ {k}                → k ∉ []
      notHere  : ∀ {i j k p ij⇿p i∉p} → k ≢ i → k ≢ j → k ∉ p → k ∉ (i , j) ∷ p ∣ ij⇿p ∣ i∉p

  _∈_ : ∀ {n : ℕ} → Fin n → SimplePathⁿᵗ n → Set
  i ∈ p = ¬ (i ∉ p)

  ------------------------------------------------------------------------------
  -- Operations

  length : ∀ {n} → SimplePathⁿᵗ n → ℕ
  length []              = 0
  length (_ ∷ p ∣ _ ∣ _) = suc (length p)

  lookupₑ : ∀ {n} → (p : SimplePathⁿᵗ n) → Fin (length p) → Fin n × Fin n
  lookupₑ []              ()
  lookupₑ (e ∷ _ ∣ _ ∣ _) fzero    = e
  lookupₑ (_ ∷ p ∣ _ ∣ _) (fsuc i) = lookupₑ p i

  data NonEmpty {n} : SimplePathⁿᵗ n → Set where
    nonEmpty : ∀ e p e⇿p e∉p → NonEmpty (e ∷ p ∣ e⇿p ∣ e∉p)

  lookupᵥ : ∀ {n} {p : SimplePathⁿᵗ n} → NonEmpty p → Fin (suc (length p)) → Fin n
  lookupᵥ (nonEmpty e p e⇿p e∉p) fzero           = proj₁ e
  lookupᵥ (nonEmpty e p e⇿p e∉p) (fsuc fzero)    = proj₂ e
  lookupᵥ (nonEmpty e [] e⇿p e∉p) (fsuc (fsuc ()))
  lookupᵥ (nonEmpty e (f ∷ p ∣ f⇿p ∣ f∉p) e⇿p e∉p) (fsuc (fsuc i)) =
    lookupᵥ (nonEmpty f p f⇿p f∉p) (fsuc i)


  -- Orders
{-
  -- Length order
  infix 4  _≤ₗ_
  _≤ₗ_ : ∀ {n} → Rel (SimplePathⁿᵗ n) ℓ₀
  p ≤ₗ q = length p ≤ℕ length q
-}
