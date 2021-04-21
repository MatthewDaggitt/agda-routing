open import Data.Fin using (Fin; _<_; _≤_) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; map)
open import Level using () renaming (zero to ℓ₀)
open import Relation.Nullary using (¬_)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

module RoutingLib.Routing.Basics.Path.Certified where

------------------------------------------------------------------------------
-- Vertices and edges

Vertex : ℕ → Set
Vertex n = Fin n

Edge : ℕ → Set
Edge n = Vertex n × Vertex n

------------------------------------------------------------------------------
-- Datatypes

mutual

  infix 4 _∈ₚ_ _∉ₚ_ _⇿_

  data Path (n : ℕ) : Set where
    []      : Path n
    _∷_∣_∣_ : ∀ e p (e⇿p : e ⇿ p) (e∉p : proj₁ e ∉ₚ p) → Path n

  data _⇿_ {n : ℕ} : Edge n → Path n → Set where
    start     : ∀ {i j}              → i ≢ j → (i , j) ⇿ []
    continue  : ∀ {i j k p jk⇿p j∉p} → i ≢ j → (i , j) ⇿ (j , k) ∷ p ∣ jk⇿p ∣ j∉p

  data _∉ₚ_ {n : ℕ} : Vertex n → Path n → Set where
    notThere : ∀ {k}                → k ∉ₚ []
    notHere  : ∀ {i j k p ij⇿p i∉p} → k ≢ i → k ≢ j → k ∉ₚ p → k ∉ₚ (i , j) ∷ p ∣ ij⇿p ∣ i∉p

_∈ₚ_ : ∀ {n} → Vertex n → Path n → Set
i ∈ₚ p = ¬ (i ∉ₚ p)

------------------------------------------------------------------------------
-- Equality

infix 4 _≈ₚ_ _≉ₚ_

data _≈ₚ_ {n} : Rel (Path n) ℓ₀ where
  []  : [] ≈ₚ []
  _∷_ : ∀ {e f p q w x y z} → e ≡ f → p ≈ₚ q → e ∷ p ∣ w ∣ x ≈ₚ f ∷ q ∣ y ∣ z

_≉ₚ_ : ∀ {n} → Rel (Path n) ℓ₀
p ≉ₚ q = ¬ (p ≈ₚ q)

------------------------------------------------------------------------------
-- Lexicographic order

infix 4 _≤ₗₑₓ_
data _≤ₗₑₓ_  {n} : Rel (Path n) ℓ₀ where
  stop  : ∀ {p} → [] ≤ₗₑₓ p
  here₁ : ∀ {i j k l p q ij⇿p kl⇿q i∉p k∉q} →
          i < k → (i , j) ∷ p ∣ ij⇿p ∣ i∉p ≤ₗₑₓ (k , l) ∷ q ∣ kl⇿q ∣ k∉q
  here₂ : ∀ {i j k l p q ij⇿p kl⇿q i∉p k∉q} →
          i ≡ k → j < l → (i , j) ∷ p ∣ ij⇿p ∣ i∉p ≤ₗₑₓ (k , l) ∷ q ∣ kl⇿q ∣ k∉q
  step  : ∀ {i j k l p q ij⇿p kl⇿q i∉p k∉q} →
          i ≡ k → j ≡ l → p ≤ₗₑₓ q  → (i , j) ∷ p ∣ ij⇿p ∣ i∉p ≤ₗₑₓ (k , l) ∷ q ∣ kl⇿q ∣ k∉q

------------------------------------------------------------------------------
-- Operations

length : ∀ {n} → Path n → ℕ
length []              = 0
length (_ ∷ p ∣ _ ∣ _) = suc (length p)

data NonEmpty {n} : Path n → Set where
  nonEmpty : ∀ e p e⇿p e∉p → NonEmpty (e ∷ p ∣ e⇿p ∣ e∉p)

lookupᵥ : ∀ {n} {p : Path n} → NonEmpty p → Fin (suc (length p)) → Fin n
lookupᵥ (nonEmpty e p e⇿p e∉p) fzero           = proj₁ e
lookupᵥ (nonEmpty e p e⇿p e∉p) (fsuc fzero)    = proj₂ e
lookupᵥ (nonEmpty e [] e⇿p e∉p) (fsuc (fsuc ()))
lookupᵥ (nonEmpty e (f ∷ p ∣ f⇿p ∣ f∉p) e⇿p e∉p) (fsuc (fsuc i)) =
  lookupᵥ (nonEmpty f p f⇿p f∉p) (fsuc i)
