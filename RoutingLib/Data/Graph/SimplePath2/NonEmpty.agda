open import Level using () renaming (zero to lzero)
open import Data.Fin using (Fin; _<_; _≤_) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (ℕ; zero; suc; _≤?_; z≤n; s≤s) renaming (_<_ to _<ℕ_; _≤_ to _≤ℕ_)
open import Data.Nat.Properties using (≰⇒>)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; map)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Decidable; Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong)
open import Function using (_∘_)

open import RoutingLib.Data.Graph renaming (_∈_ to _∈𝔼_)

module RoutingLib.Data.Graph.SimplePath2.NonEmpty where

  ---------------------
  -- Non-empty paths --
  ---------------------

  mutual

    infix 4 _∉_ _⇿_
    
    data SimplePathⁿᵗ (n : ℕ) : Set lzero where
      []      : SimplePathⁿᵗ n
      _∷_∣_∣_ : ∀ e p (e⇿p : e ⇿ p) (e∉p : proj₁ e ∉ p) → SimplePathⁿᵗ n
    
    data _⇿_ {n : ℕ} : Fin n × Fin n → SimplePathⁿᵗ n → Set lzero where
      start     : ∀ {i j}              → i ≢ j → (i , j) ⇿ [] 
      continue  : ∀ {i j k p jk⇿p j∉p} → i ≢ j → (i , j) ⇿ (j , k) ∷ p ∣ jk⇿p ∣ j∉p
    
    data _∉_ {n : ℕ} : Fin n → SimplePathⁿᵗ n → Set lzero where
      notThere : ∀ {k}                  → k ∉ []
      notHere  : ∀ {i j k p ij⇿p i∉p} → k ≢ i → k ≢ j → k ∉ p → k ∉ (i , j) ∷ p ∣ ij⇿p ∣ i∉p

  -- Equality
  
  infix 4 _≈_ _≉_

  data _≈_ {n : ℕ} : Rel (SimplePathⁿᵗ n) lzero where
    []  : [] ≈ []
    _∷_ : ∀ {e f p q e⇿p f⇿q e∉p f∉q} → e ≡ f → p ≈ q → (e ∷ p ∣ e⇿p ∣ e∉p) ≈ (f ∷ q ∣ f⇿q ∣ f∉q)

  _≉_ : ∀ {n} → Rel (SimplePathⁿᵗ n) lzero
  p ≉ q = ¬ (p ≈ q)

  -- Operations

  length : ∀ {n} → SimplePathⁿᵗ n → ℕ
  length []              = 1
  length (_ ∷ p ∣ _ ∣ _) = suc (length p)
  
 {-
  _⟦_⟧ : ∀ {n} → (p : SimplePathⁿᵗ n) → Fin (suc (length p)) → Fin n
  (i ∺ _ ∣ _) ⟦ fzero ⟧          = i
  (_ ∺ j ∣ _) ⟦ fsuc fzero ⟧     = j
  (_ ∺ _ ∣ _) ⟦ fsuc (fsuc ()) ⟧ 
  (i ∷ _ ∣ _) ⟦ fzero ⟧          = i
  (_ ∷ p ∣ _) ⟦ fsuc k ⟧         = p ⟦ k ⟧
-}

  ----------------------------------------------------------------------------------------------
  -- Orders


  infix 4 _≤ₗₑₓ_ _≤ₗ_
  -- Lexicographic order
  data _≤ₗₑₓ_ {n : ℕ} : Rel (SimplePathⁿᵗ n) lzero where
    stop  : ∀ {p} → [] ≤ₗₑₓ p
    here₁ : ∀ {i j k l p q ij⇿p kl⇿q i∉p k∉q} →
            i < k → (i , j) ∷ p ∣ ij⇿p ∣ i∉p ≤ₗₑₓ (k , l) ∷ q ∣ kl⇿q ∣ k∉q
    here₂ : ∀ {i j k l p q ij⇿p kl⇿q i∉p k∉q} →
            i ≡ k → j < l → (i , j) ∷ p ∣ ij⇿p ∣ i∉p ≤ₗₑₓ (k , l) ∷ q ∣ kl⇿q ∣ k∉q
    step  : ∀ {i j k l p q ij⇿p kl⇿q i∉p k∉q} →
            i ≡ k → j ≡ l → p ≤ₗₑₓ q  → (i , j) ∷ p ∣ ij⇿p ∣ i∉p ≤ₗₑₓ (k , l) ∷ q ∣ kl⇿q ∣ k∉q

  -- Length order
  _≤ₗ_ : ∀ {n} → Rel (SimplePathⁿᵗ n) lzero
  p ≤ₗ q = length p ≤ℕ length q

  -- Combined order

  data _≤ₚ_ {n : ℕ} :  Rel (SimplePathⁿᵗ n) lzero where
    stop₁ : ∀ {q}     → [] ≤ₚ q
    len   : ∀ {p} {q} → length p <ℕ length q → p ≤ₚ q
    lex   : ∀ {p} {q} → length p ≡ length q → p ≤ₗₑₓ q → p ≤ₚ q
    
  -- Exists in graph
  
{-
  infix 4 _∈𝔾_ _∉𝔾_

  data _∈𝔾_ {a n} {A : Set a} : SimplePathⁿᵗ n → Graph A n → Set a where
    edge-∺ : ∀ {G i j i≢j} → (i , j) ∈𝔼 G → i ∺ j ∣ i≢j ∈𝔾 G
    edge-∷ : ∀ {G i p i≢p₀} → (i , source p) ∈𝔼 G → p ∈𝔾 G → i ∷ p ∣ i≢p₀ ∈𝔾 G

  _∉𝔾_ : ∀ {a n} {A : Set a} → SimplePathⁿᵗ n → Graph A n → Set a
  p ∉𝔾 G = ¬ p ∈𝔾 G

  weight : ∀ {a b} {A : Set a} {B : Set b} → (A → B → B) → B → ∀ {n} {G : Graph A n} {p} → p ∈𝔾 G → B
  weight _▷_ 1# (edge-∺ (v , _))     = v ▷ 1#
  weight _▷_ 1# (edge-∷ (v , _) p∈G) = v ▷ weight _▷_ 1# p∈G

-}
