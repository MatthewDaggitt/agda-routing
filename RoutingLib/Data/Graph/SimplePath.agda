open import Level using () renaming (zero to lzero)
open import Data.Fin using (Fin; _<_; _≤_) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (ℕ; zero; suc; _≤?_; z≤n; s≤s) renaming (_<_ to _<ℕ_)
open import Data.Nat.Properties using (≰⇒>)
open import Data.Product using (_,_)
open import Data.List using (List; []; _∷_; map)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Decidable; Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong)
open import Function using (_∘_)

open import RoutingLib.Data.Graph using (Graph)
open import RoutingLib.Data.Graph.SimplePath.NonEmpty as NT using (SimplePathⁿᵗ; _≤ₗₑₓ_)

module RoutingLib.Data.Graph.SimplePath where

  open import RoutingLib.Data.Graph.SimplePath.NonEmpty using (_∺_∣_; _∷_∣_; _∷_; _∺_; stopFirst; stopSecond; stepUnequal; stepEqual; edge-∺; edge-∷; source; destination) public

  infix 4 _∉_ _≈_ _≉_

  -- Data type

  data SimplePath (n : ℕ) : Set lzero where
    []  : SimplePath n
    [_] : SimplePathⁿᵗ n → SimplePath n


  -- Membership

  data _∉_ {n : ℕ} : Fin n → SimplePath n → Set lzero where
    [] : ∀ {i} → i ∉ []
    [_] : ∀ {i p} → i NT.∉ p → i ∉ [ p ]

  _∈_ : ∀ {n} → Fin n → SimplePath n → Set lzero
  i ∈ p = ¬ (i ∉ p)


  -- Equality

  data _≈_ {n : ℕ} : Rel (SimplePath n) lzero where
    [] : [] ≈ []
    [_] : ∀ {p q} → p NT.≈ q → [ p ] ≈ [ q ]

  _≉_ : ∀ {n} → Rel (SimplePath n) lzero
  xs ≉ ys = ¬ (xs ≈ ys)


  -- Orderings

  infix 4 _≤ₚ_ _≰ₚ_

  data _≤ₚ_ {n : ℕ} : Rel (SimplePath n) lzero where
    stop : ∀ {p} → [] ≤ₚ p
    len  : ∀ {p} {q} → NT.length p <ℕ NT.length q → [ p ] ≤ₚ [ q ]
    lex  : ∀ {p} {q} → NT.length p ≡ NT.length q → p ≤ₗₑₓ q → [ p ] ≤ₚ [ q ]

  _≰ₚ_ : ∀ {n} → Rel (SimplePath n) lzero
  p ≰ₚ q = ¬ (p ≤ₚ q)


  -- Exists in graph

  data _∈𝔾_ {a} {n : ℕ} {A : Set a} : SimplePath n → Graph A n → Set a where
    []  : ∀ {G} → [] ∈𝔾 G
    [_] : ∀ {G p} → p NT.∈𝔾 G → [ p ] ∈𝔾 G


  ----------------
  -- Operations --
  ----------------

  length : ∀ {n} → SimplePath n → ℕ
  length [] = 0
  length [ p ] = NT.length p

  weight : ∀ {a b} {A : Set a} {B : Set b} → (A → B → B) → B → ∀ {n} {G : Graph A n} {p} → p ∈𝔾 G → B
  weight _▷_ 1# []      = 1#
  weight _▷_ 1# [ p∈G ] = NT.weight _▷_ 1# p∈G
