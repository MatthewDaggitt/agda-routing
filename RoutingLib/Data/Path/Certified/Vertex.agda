open import Data.Fin using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary using (Rel)

open import RoutingLib.Data.Path.NonEmpty as NT using (Pathⁿᵗ)

module RoutingLib.Data.VertexPath where

  ----------------------------------------------------------------------------
  -- Datatype

  open NT using ([]; _∷_∣_∣_; notHere; notThere; continue) public

  data Path : Set where
    invalid : Path
    valid   : Pathⁿᵗ → Path

  ----------------------------------------------------------------------------
  -- Linkage

  open NT using (continue) public

  infix 4 _⇿_

  data _⇿_ : ℕ × ℕ → Path → Set where
    valid : ∀ {e p} → e NT.⇿ p → e ⇿ valid p

  ----------------------------------------------------------------------------
  -- Membership

  open NT using (notHere; notThere) public

  infix 4 _∉_ _∈_

  data _∉_ : ℕ → Path → Set where
    invalid : ∀ {i} → i ∉ invalid
    valid   : ∀ {i p} → i NT.∉ p → i ∉ valid p

  _∈_ : ℕ → Path → Set
  i ∈ p = ¬ (i ∉ p)


  ----------------------------------------------------------------------------
  -- Operations

  length : Path → ℕ
  length invalid   = 0
  length (valid p) = NT.length p





{-
  -- Orderings

  infix 4 _≤ₚ_ _≰ₚ_

  data _≤ₚ_ {n : ℕ} : Rel (Path n) lzero where
    empty : ∀ {p} → ∅ ≤ₚ p
    stop₁ : [] ≤ₚ []
    stop₂ : ∀ {p} → [] ≤ₚ [ p ]
    len   : ∀ {p} {q} → NT.length p <ℕ NT.length q → [ p ] ≤ₚ [ q ]
    lex   : ∀ {p} {q} → NT.length p ≡ NT.length q → p ≤ₗₑₓ q → [ p ] ≤ₚ [ q ]

  _≰ₚ_ : ∀ {n} → Rel (Path n) lzero
  p ≰ₚ q = ¬ (p ≤ₚ q)



  infixr 5 _∷ₐ_

  _∷ₐ_ : ∀ {n} → Fin n × Fin n → Path n → Path n
  _       ∷ₐ invalid = invalid
  (i , j) ∷ₐ valid p with (i , j) NTP.⇿? p | i NTP.∉? p
  ... | no _     | _       = invalid
  ... | _        | no  _   = invalid
  ... | yes ij⇿p | yes i∉p = valid ((i , j) ∷ p ∣ ij⇿p ∣ i∉p)
-}
