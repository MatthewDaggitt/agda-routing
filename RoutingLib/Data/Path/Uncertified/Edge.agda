open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; _≟_)
open import Data.Maybe as Maybe using (Maybe; maybe′) hiding (module Maybe)
open import Data.Product using (_×_; _,_)
open import Data.List as List using (List) hiding (module List)
open import Data.List.Any using (Any)
open import Level using () renaming (zero to 0ℓ)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

module RoutingLib.Data.Path.Uncertified.FiniteEdges where

----------------------------------------------------------------------------
-- Vertices

Vertex : ℕ → Set
Vertex = Fin

----------------------------------------------------------------------------
-- Edges

Edge : ℕ → Set
Edge n = Vertex n × Vertex n

infix 4 _∈ₑ_
  
data _∈ₑ_ : ∀ {n} → Vertex n → Edge n → Set where
  left  : ∀ {n} {i j : Fin n} → i ∈ₑ (i , j)
  right : ∀ {n} {i j : Fin n} → j ∈ₑ (i , j)

----------------------------------------------------------------------------
-- Valid paths

open List public using ([]; _∷_)

ValidPath : ℕ → Set
ValidPath n = List (Edge n)

infix 4 _∈ᵥₚ_ _∉ᵥₚ_
  
_∈ᵥₚ_ : ∀ {n} → Vertex n → ValidPath n → Set
i ∈ᵥₚ p = Any (i ∈ₑ_) p

_∉ᵥₚ_ : ∀ {n} → Vertex n → ValidPath n → Set
i ∉ᵥₚ p = ¬ (i ∈ᵥₚ p)



infix 4 _⇿ᵥₚ_
  
data _⇿ᵥₚ_ : ∀ {n} → Edge n → ValidPath n → Set where
  start    : ∀ {n} {i j : Fin n}   → (i , j) ⇿ᵥₚ []
  continue : ∀ {n} {i j k : Fin n} → (i , j) ⇿ᵥₚ ((j , k) ∷ [])


postulate _⇿?_ : ∀ {n} (e : Edge n) (p : ValidPath n) → Dec (e ⇿ᵥₚ p)

postulate _∈?_ : ∀ {n} (i : Vertex n) (p : ValidPath n) → Dec (i ∈ᵥₚ p)

----------------------------------------------------------------------------
-- Paths

Path : ℕ → Set
Path n = Maybe (ValidPath n)

open Maybe public using ()
  renaming
  ( nothing to invalid
  ; just    to valid
  )

_∷ₚ_ : ∀ {n} → Edge n → Path n → Path n
(i , j) ∷ₚ invalid       = invalid
(i , j) ∷ₚ valid []      = valid ((i , j) ∷ [])
(i , j) ∷ₚ valid ((k , l) ∷ p) with j ≟ k
... | no  _    = invalid
... | yes refl = valid ((i , j) ∷ (j , l) ∷ p)

_∈ₚ_ : ∀ {n} → Vertex n → Path n → Set
i ∈ₚ p = Maybe.All (i ∈ᵥₚ_) p

_∉ₚ_ : ∀ {n} → Vertex n → Path n → Set
i ∉ₚ p = ¬ (i ∈ₚ p)

postulate p≢e∷p : ∀ {n} {e : Edge n} {p : ValidPath n} → _≢_ {A = Path n} (valid p) (valid (e ∷ p))

----------------------------------------------------------------------------
-- Operations

length : ∀ {n} → Path n → ℕ
length = maybe′ List.length 0
