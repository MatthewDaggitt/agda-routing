open import Data.Fin using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary using (Rel)

open import RoutingLib.Data.SimplePath.NonEmpty as NT using (SimplePathⁿᵗ)

module RoutingLib.Data.SimplePath where

  ----------------------------------------------------------------------------
  -- Datatype
    
  open NT using ([]; _∷_∣_∣_; notHere; notThere; continue) public

  data SimplePath (n : ℕ) : Set where
    invalid : SimplePath n
    valid   : SimplePathⁿᵗ n → SimplePath n

  ----------------------------------------------------------------------------
  -- Linkage
  
  open NT using (continue) public
  
  infix 4 _⇿_
  
  data _⇿_ {n : ℕ} : Fin n × Fin n → SimplePath n → Set where
    valid : ∀ {e p} → e NT.⇿ p → e ⇿ valid p

  ----------------------------------------------------------------------------
  -- Membership

  open NT using (notHere; notThere) public
  
  infix 4 _∉_ _∈_
  
  data _∉_ {n : ℕ} : Fin n → SimplePath n → Set where
    invalid : ∀ {i} → i ∉ invalid
    valid   : ∀ {i p} → i NT.∉ p → i ∉ valid p

  _∈_ : ∀ {n} → Fin n → SimplePath n → Set
  i ∈ p = ¬ (i ∉ p)


  ----------------------------------------------------------------------------
  -- Operations
  
  length : ∀ {n} → SimplePath n → ℕ
  length invalid   = 0
  length (valid p) = NT.length p

  
  

  
{-
  -- Orderings

  infix 4 _≤ₚ_ _≰ₚ_

  data _≤ₚ_ {n : ℕ} : Rel (SimplePath n) lzero where
    empty : ∀ {p} → ∅ ≤ₚ p
    stop₁ : [] ≤ₚ []
    stop₂ : ∀ {p} → [] ≤ₚ [ p ]
    len   : ∀ {p} {q} → NT.length p <ℕ NT.length q → [ p ] ≤ₚ [ q ]
    lex   : ∀ {p} {q} → NT.length p ≡ NT.length q → p ≤ₗₑₓ q → [ p ] ≤ₚ [ q ]

  _≰ₚ_ : ∀ {n} → Rel (SimplePath n) lzero
  p ≰ₚ q = ¬ (p ≤ₚ q)


  
  infixr 5 _∷ₐ_
  
  _∷ₐ_ : ∀ {n} → Fin n × Fin n → SimplePath n → SimplePath n
  _       ∷ₐ invalid = invalid
  (i , j) ∷ₐ valid p with (i , j) NTP.⇿? p | i NTP.∉? p
  ... | no _     | _       = invalid
  ... | _        | no  _   = invalid
  ... | yes ij⇿p | yes i∉p = valid ((i , j) ∷ p ∣ ij⇿p ∣ i∉p)
-}
