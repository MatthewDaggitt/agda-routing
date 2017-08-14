open import Level using () renaming (zero to lzero)
open import Data.Fin using (Fin; _<_; _≤_) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (ℕ; zero; suc; _≤?_; z≤n; s≤s) renaming (_<_ to _<ℕ_; _≤_ to _≤ℕ_)
open import Data.Nat.Properties using (≰⇒>)
open import Data.Product using (_,_)
open import Data.List using (List; []; _∷_; map)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Decidable; Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong)
open import Function using (_∘_)

open import RoutingLib.Data.Graph renaming (_∈_ to _∈𝔼_)

module RoutingLib.Data.Graph.SimplePath.NonEmpty where

  ---------------------
  -- Non-empty paths --
  ---------------------

  mutual

    data SimplePathⁿᵗ (n : ℕ) : Set lzero where
      _∺_∣_ : ∀ (i j : Fin n) → i ≢ j → SimplePathⁿᵗ n
      _∷_∣_ : ∀ i p → i ∉ p → SimplePathⁿᵗ n

    infix 4 _∉_
    
    data _∉_ {n : ℕ} : Fin n → SimplePathⁿᵗ n → Set lzero where
      notThere : ∀ {i j k i≢j} → k ≢ i → k ≢ j   → k ∉ i ∺ j ∣ i≢j
      notHere  : ∀ {i p k i∉p} → k ≢ i → k ∉ p → k ∉ i ∷ p ∣ i∉p


  -- Equality 

  infix 4 _≈_ _≉_

  data _≈_ {n : ℕ} : Rel (SimplePathⁿᵗ n) lzero where
    _∺_ : ∀ {i j k l i≢j k≢l} → i ≡ k → j ≡ l → (i ∺ j ∣ i≢j) ≈ (k ∺ l ∣ k≢l)
    _∷_ : ∀ {i j p q i∉p j∉q} → i ≡ j → p ≈ q → (i ∷ p ∣ i∉p) ≈ (j ∷ q ∣ j∉q)

  _≉_ : ∀ {n} → Rel (SimplePathⁿᵗ n) lzero
  p ≉ q = ¬ (p ≈ q)
 

  -- Operations

  source : ∀ {n} → SimplePathⁿᵗ n → Fin n
  source (i ∺ _ ∣ _) = i
  source (i ∷ _ ∣ _) = i

  destination : ∀ {n} → SimplePathⁿᵗ n → Fin n
  destination (_ ∺ j ∣ _) = j
  destination (_ ∷ p ∣ _) = destination p

  length : ∀ {n} → SimplePathⁿᵗ n → ℕ
  length (_ ∺ _ ∣ _) = 1
  length (_ ∷ p ∣ _) = suc (length p)
 
  _⟦_⟧ : ∀ {n} → (p : SimplePathⁿᵗ n) → Fin (suc (length p)) → Fin n
  (i ∺ _ ∣ _) ⟦ fzero ⟧          = i
  (_ ∺ j ∣ _) ⟦ fsuc fzero ⟧     = j
  (_ ∺ _ ∣ _) ⟦ fsuc (fsuc ()) ⟧ 
  (i ∷ _ ∣ _) ⟦ fzero ⟧          = i
  (_ ∷ p ∣ _) ⟦ fsuc k ⟧         = p ⟦ k ⟧

  ----------------------------------------------------------------------------------------------
  -- Orders

  infix 4 _≤ₗₑₓ_ _≤ₗ_
  -- Lexicographic order
  data _≤ₗₑₓ_ {n : ℕ} : Rel (SimplePathⁿᵗ n) lzero where
    stopFirst   : ∀ {i j k l i≢j k≢l} → i ≡ k → j ≤ l → i ∺ j ∣ i≢j ≤ₗₑₓ k ∺ l ∣ k≢l
    stopSecond  : ∀ {i j k l i≢j k≢l} → i < k → i ∺ j ∣ i≢j ≤ₗₑₓ k ∺ l ∣ k≢l
    stepUnequal : ∀ {i j p q i∉p j∉q} → i < j → i ∷ p ∣ i∉p ≤ₗₑₓ j ∷ q ∣ j∉q
    stepEqual   : ∀ {i j p q i∉p j∉q} → i ≡ j → p ≤ₗₑₓ q → i ∷ p ∣ i∉p ≤ₗₑₓ j ∷ q ∣ j∉q

  -- Length order
  _≤ₗ_ : ∀ {n} → Rel (SimplePathⁿᵗ n) lzero
  p ≤ₗ q = length p ≤ℕ length q

  
  -- Exists in graph

  infix 4 _∈𝔾_ _∉𝔾_

  data _∈𝔾_ {a n} {A : Set a} : SimplePathⁿᵗ n → Graph A n → Set a where
    edge-∺ : ∀ {G i j i≢j} → (i , j) ∈𝔼 G → i ∺ j ∣ i≢j ∈𝔾 G
    edge-∷ : ∀ {G i p i≢p₀} → (i , source p) ∈𝔼 G → p ∈𝔾 G → i ∷ p ∣ i≢p₀ ∈𝔾 G

  _∉𝔾_ : ∀ {a n} {A : Set a} → SimplePathⁿᵗ n → Graph A n → Set a
  p ∉𝔾 G = ¬ p ∈𝔾 G
  
  weight : ∀ {a b} {A : Set a} {B : Set b} → (A → B → B) → B → ∀ {n} {G : Graph A n} {p} → p ∈𝔾 G → B
  weight _▷_ 1# (edge-∺ (v , _))     = v ▷ 1#
  weight _▷_ 1# (edge-∷ (v , _) p∈G) = v ▷ weight _▷_ 1# p∈G
