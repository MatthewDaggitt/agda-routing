open import Level using () renaming (zero to lzero)
open import Data.Fin using (Fin; _<_; _≤_) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (ℕ; zero; suc; _≤?_; z≤n; s≤s) renaming (_<_ to _<ℕ_)
open import Data.Nat.Properties using (≰⇒>)
open import Data.Product using (_,_; _×_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Decidable; Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong)
open import Function using (_∘_)

open import RoutingLib.Data.Graph.SimplePath2.NonEmpty as NT using (SimplePathⁿᵗ; _≤ₗₑₓ_)
import RoutingLib.Data.Graph.SimplePath2.NonEmpty.Properties as NTP

module RoutingLib.Data.Graph.SimplePath2 where

  open import RoutingLib.Data.Graph.SimplePath2.NonEmpty using ([]; _∷_; _∷_∣_∣_; stop; here₁; here₂; step) public

  infix 4 _≈_ _≉_ _∉_ _∈_ _⇿_

  -- Data type

  data SimplePath (n : ℕ) : Set lzero where
    invalid : SimplePath n
    valid   : SimplePathⁿᵗ n → SimplePath n

  infixr 5 _∷ₐ_
  
  _∷ₐ_ : ∀ {n} → Fin n × Fin n → SimplePath n → SimplePath n
  _       ∷ₐ invalid = invalid
  (i , j) ∷ₐ valid p with (i , j) NTP.⇿? p | i NTP.∉? p
  ... | no _     | _       = invalid
  ... | _        | no  _   = invalid
  ... | yes ij⇿p | yes i∉p = valid ((i , j) ∷ p ∣ ij⇿p ∣ i∉p)


  -- Linkage

  data _⇿_ {n : ℕ} : Fin n × Fin n → SimplePath n → Set lzero where
    valid : ∀ {e p} → e NT.⇿ p → e ⇿ valid p

  -- Membership
  
  data _∉_ {n : ℕ} : Fin n → SimplePath n → Set lzero where
    invalid : ∀ {i} → i ∉ invalid
    valid   : ∀ {i p} → i NT.∉ p → i ∉ valid p

  _∈_ : ∀ {n} → Fin n → SimplePath n → Set lzero
  i ∈ p = ¬ (i ∉ p)

  -- Equality

  data _≈_ {n : ℕ} : Rel (SimplePath n) lzero where
    invalid : invalid  ≈ invalid
    valid   : ∀ {p q} → p NT.≈ q → valid p ≈ valid q

  _≉_ : ∀ {n} → Rel (SimplePath n) lzero
  xs ≉ ys = ¬ (xs ≈ ys)
  
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


  -- Exists in graph

  data _∈𝔾_ {a} {n : ℕ} {A : Set a} : SimplePath n → Graph A n → Set a where
    []  : ∀ {G} → [] ∈𝔾 G
    [_] : ∀ {G p} → p NT.∈𝔾 G → [ p ] ∈𝔾 G

  _∉𝔾_ : ∀ {a n} {A : Set a} → SimplePath n → Graph A n → Set a
  p ∉𝔾 G = ¬ (p ∈𝔾 G) 

  ----------------
  -- Operations --
  ----------------

-}
  length : ∀ {n} → SimplePath n → ℕ
  length invalid   = 0
  length (valid p) = NT.length p
