open import Data.Fin using (Fin; _≤_) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; _<_; zero; suc; _≟_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Any using (Any)
open import Level using () renaming (zero to ℓ₀)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
import Relation.Binary.Construct.NonStrictToStrict as ToStrict

module RoutingLib.Data.Path.Uncertified where

------------------------------------------------------------------------------
-- Vertices and edges

Vertex : Set
Vertex = ℕ

Edge : Set
Edge = Vertex × Vertex

------------------------------------------------------------------------------
-- Datatypes

open Data.List public using ([]; _∷_)

Path : Set
Path = List Edge

------------------------------------------------------------------------------
-- Membership

infix 4 _∈ₑ_ _∈ₚ_ _∉ₚ_

data _∈ₑ_ : Vertex → Edge → Set where
  left  : ∀ {i j} → i ∈ₑ (i , j)
  right : ∀ {i j} → j ∈ₑ (i , j)
  
_∈ₚ_ : Vertex → Path → Set
i ∈ₚ p = Any (i ∈ₑ_) p

_∉ₚ_ : Vertex → Path → Set
i ∉ₚ p = ¬ (i ∈ₚ p)

------------------------------------------------------------------------------
-- Linking

infix 4 _⇿_

data _⇿_ : Edge → Path → Set where
  start     : ∀ {i j}     (i≢j : i ≢ j) → (i , j) ⇿ []
  continue  : ∀ {i j k p} (i≢j : i ≢ j) → (i , j) ⇿ (j , k) ∷ p

------------------------------------------------------------------------------
-- Equality

infix 4 _≈ₚ_ _≉ₚ_

_≈ₚ_ : Rel Path ℓ₀
_≈ₚ_ = _≡_

_≉ₚ_ : Rel Path ℓ₀
p ≉ₚ q = ¬ (p ≈ₚ q)

------------------------------------------------------------------------------
-- Lexicographic order

infix 4 _≤ₗₑₓ_

data _≤ₗₑₓ_ : Rel Path ℓ₀ where
  stop  : ∀ {p} → [] ≤ₗₑₓ p
  here₁ : ∀ {i j k l p q} → i < k → (i , j) ∷ p ≤ₗₑₓ (k , l) ∷ q
  here₂ : ∀ {i j k l p q} → i ≡ k → j < l → (i , j) ∷ p ≤ₗₑₓ (k , l) ∷ q
  step  : ∀ {i j k l p q} → i ≡ k → j ≡ l → p ≤ₗₑₓ q  → (i , j) ∷ p  ≤ₗₑₓ (k , l) ∷ q

open ToStrict _≡_ _≤ₗₑₓ_ public
  using () renaming (_<_ to _<ₗₑₓ_)

------------------------------------------------------------------------------
-- Operations

length : Path → ℕ
length []      = 0
length (_ ∷ p) = suc (length p)

inflate : Path → ℕ → Path
inflate p               zero    = p
inflate []              (suc n) = []
inflate q@((i , j) ∷ p) (suc n) = (i , i) ∷ inflate q n

deflate : Path → Path
deflate [] = []
deflate ((i , j) ∷ p) with i ≟ j
... | yes _ = deflate p
... | no  _ = (i , j) ∷ p
