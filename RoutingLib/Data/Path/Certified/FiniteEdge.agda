open import Data.Fin using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Level using () renaming (zero to 0ℓ)
open import Relation.Nullary using (¬_)
open import Relation.Binary using (Rel)

open import RoutingLib.Data.Path.Certified.FiniteEdge.NonEmpty as NT using (Pathⁿᵗ)

module RoutingLib.Data.Path.Certified.FiniteEdge where

----------------------------------------------------------------------------
-- Datatype

open NT using (Edge; Vertex; []; _∷_∣_∣_; notHere; notThere; continue) public

data Path (n : ℕ) : Set where
  invalid : Path n
  valid   : Pathⁿᵗ n → Path n

----------------------------------------------------------------------------
-- Linkage

open NT using (continue) public

infix 4 _⇿_

data _⇿_ {n : ℕ} : Fin n × Fin n → Path n → Set where
  valid : ∀ {e p} → e NT.⇿ p → e ⇿ valid p

----------------------------------------------------------------------------
-- Membership

open NT using (notHere; notThere) public

infix 4 _∉_ _∈_

data _∉_ {n : ℕ} : Vertex n → Path n → Set where
  invalid : ∀ {i} → i ∉ invalid
  valid   : ∀ {i p} → i NT.∉ p → i ∉ valid p

_∈_ : ∀ {n} → Vertex n → Path n → Set
i ∈ p = ¬ (i ∉ p)

----------------------------------------------------------------------------
-- Equality

open NT using ([]; _∷_) public

infix 4 _≈ₚ_ _≉ₚ_

data _≈ₚ_ {n} : Rel (Path n) 0ℓ where
  invalid : invalid  ≈ₚ invalid
  valid   : ∀ {p q} → p NT.≈ₚ q → valid p ≈ₚ valid q

_≉ₚ_ : ∀ {n} → Rel (Path n) 0ℓ
xs ≉ₚ ys = ¬ (xs ≈ₚ ys)

----------------------------------------------------------------------------
-- Operations

length : ∀ {n} → Path n → ℕ
length invalid   = 0
length (valid p) = NT.length p
