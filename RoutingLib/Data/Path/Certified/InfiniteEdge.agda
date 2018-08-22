open import Data.Fin using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred; Decidable)

open import RoutingLib.Data.Path.EdgePath.NonEmpty as NT using (Pathⁿᵗ)

module RoutingLib.Data.Path.EdgePath where

  ----------------------------------------------------------------------------
  -- Datatype

  open NT using (Edge; []; _∷_∣_∣_; notHere; notThere; continue) public

  data Path : Set where
    invalid : Path
    valid   : (p : Pathⁿᵗ) → Path

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

  count : ∀ {a} {P : Pred ℕ a} → Decidable P → Path → ℕ
  count P? invalid   = 0
  count P? (valid p) = NT.count P? p
