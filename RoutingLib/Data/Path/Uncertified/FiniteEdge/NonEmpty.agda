open import Data.Fin using (Fin; _<_; _≤_) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Any using (Any)
open import Level using () renaming (zero to ℓ₀)
open import Relation.Nullary using (¬_)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
import Relation.Binary.NonStrictToStrict as ToStrict

module RoutingLib.Data.Path.Uncertified.FiniteEdge.NonEmpty where

------------------------------------------------------------------------------
-- Vertices and edges

Vertex : ℕ → Set
Vertex = Fin

Edge : ℕ → Set
Edge n = Vertex n × Vertex n

------------------------------------------------------------------------------
-- Datatypes

open Data.List public using ([]; _∷_)

Pathⁿᵗ : ℕ → Set
Pathⁿᵗ n = List (Edge n)

------------------------------------------------------------------------------
-- Membership

infix 4 _∈_ _∉_

data _∈ₑ_ {n} : Vertex n → Edge n → Set where
  left  : ∀ {i j} → i ∈ₑ (i , j)
  right : ∀ {i j} → j ∈ₑ (i , j)
  
_∈_ : ∀ {n} → Vertex n → Pathⁿᵗ n → Set
i ∈ p = Any (i ∈ₑ_) p

_∉_ : ∀ {n} → Vertex n → Pathⁿᵗ n → Set
i ∉ p = ¬ (i ∈ p)

------------------------------------------------------------------------------
-- Linking

infix 4 _⇿_

data _⇿_ {n : ℕ} : Edge n → Pathⁿᵗ n → Set where
  start     : ∀ {i j}     → i ≢ j → (i , j) ⇿ []
  continue  : ∀ {i j k p} → i ≢ j → (i , j) ⇿ (j , k) ∷ p

------------------------------------------------------------------------------
-- Equality

infix 4 _≈ₚ_ _≉ₚ_

_≈ₚ_ : ∀ {n} → Rel (Pathⁿᵗ n) ℓ₀
_≈ₚ_ = _≡_

_≉ₚ_ : ∀ {n} → Rel (Pathⁿᵗ n) ℓ₀
p ≉ₚ q = ¬ (p ≈ₚ q)

------------------------------------------------------------------------------
-- Lexicographic order

module _ {n : ℕ} where

  infix 4 _≤ₗₑₓ_

  data _≤ₗₑₓ_ : Rel (Pathⁿᵗ n) ℓ₀ where
    stop  : ∀ {p} → [] ≤ₗₑₓ p
    here₁ : ∀ {i j k l p q} → i < k → (i , j) ∷ p ≤ₗₑₓ (k , l) ∷ q
    here₂ : ∀ {i j k l p q} → i ≡ k → j < l → (i , j) ∷ p ≤ₗₑₓ (k , l) ∷ q
    step  : ∀ {i j k l p q} → i ≡ k → j ≡ l → p ≤ₗₑₓ q  → (i , j) ∷ p  ≤ₗₑₓ (k , l) ∷ q

  open ToStrict _≡_ _≤ₗₑₓ_ public
    using () renaming (_<_ to _<ₗₑₓ_)

------------------------------------------------------------------------------
-- Operations

length : ∀ {n} → Pathⁿᵗ n → ℕ
length []      = 0
length (_ ∷ p) = suc (length p)

{-
data NonEmpty {n} : Pathⁿᵗ n → Set where
  nonEmpty : ∀ e p e⇿p e∉p → NonEmpty (e ∷ p ∣ e⇿p ∣ e∉p)

lookupᵥ : ∀ {n} {p : Pathⁿᵗ n} → NonEmpty p → Fin (suc (length p)) → Fin n
lookupᵥ (nonEmpty e p e⇿p e∉p) fzero           = proj₁ e
lookupᵥ (nonEmpty e p e⇿p e∉p) (fsuc fzero)    = proj₂ e
lookupᵥ (nonEmpty e [] e⇿p e∉p) (fsuc (fsuc ()))
lookupᵥ (nonEmpty e (f ∷ p ∣ f⇿p ∣ f∉p) e⇿p e∉p) (fsuc (fsuc i)) =
  lookupᵥ (nonEmpty f p f⇿p f∉p) (fsuc i)
-}
