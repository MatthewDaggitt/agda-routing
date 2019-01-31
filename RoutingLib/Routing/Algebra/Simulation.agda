--------------------------------------------------------------------------------
-- This module defines the notion of an algebra A simulating another algebra B.
-- In such a case the behaviour of B can be reasoned about using the behaviour
-- of A.
--------------------------------------------------------------------------------

open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.Algebra.Simulation
  {a₁ a₂ b₁ b₂ ℓ₁ ℓ₂}
  (A : RawRoutingAlgebra a₁ b₁ ℓ₁)
  (B : RawRoutingAlgebra a₂ b₂ ℓ₂)
  where

open import Data.Fin using (Fin)
open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_)

import RoutingLib.Routing.Algebra.Comparable as Comparable

open RawRoutingAlgebra hiding (_≟_)
open RawRoutingAlgebra A using ()
  renaming (_≈_ to _≈ᵃ_; _⊕_ to _⊕ᵃ_; _▷_ to _▷ᵃ_; 0# to 0#ᵃ; ∞ to ∞ᵃ; f∞ to f∞ᵃ)
open RawRoutingAlgebra B using ()
  renaming (_≈_ to _≈ᵇ_; _⊕_ to _⊕ᵇ_; _▷_ to _▷ᵇ_; 0# to 0#ᵇ; ∞ to ∞ᵇ; f∞ to f∞ᵇ)

--------------------------------------------------------------------------------
-- Definition

record Simulates : Set (lsuc (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂ ⊔ ℓ₁ ⊔ ℓ₂))where
  open Comparable A

  field
    to        : Route A → Route B
    from      : Route B → Route A
    to-from   : ∀ x → to (from x) ≈ᵇ x

    toₛ       : ∀ {n} {i j : Fin n} → Step A i j → Step B i j
    fromₛ     : ∀ {n} {i j : Fin n} → Step B i j → Step A i j
    toₛ-fromₛ : ∀ {n} {i j : Fin n} (e : Step B i j) → toₛ (fromₛ e) ≡ e

    to-0#     : to 0#ᵃ ≈ᵇ 0#ᵇ
    to-∞      : to ∞ᵃ  ≈ᵇ ∞ᵇ
    to-cong   : ∀ {x y} → x ≈ᵃ y → to x ≈ᵇ to y
    to-▷      : ∀ {n} {i j : Fin n} (f : Step A i j) x → to (f  ▷ᵃ x) ≈ᵇ toₛ f ▷ᵇ to x
    to-f∞     : ∀ {n} {i j : Fin n} → toₛ (f∞ᵃ i j) ≡ f∞ᵇ i j
    
    -- Note that A need only simulate B's choice for routes that are comparable.
    -- This allows only "morally" commutative routing algebras to be proved correct.
    to-⊕     : ∀ {x y} → x ≎ y → to x ⊕ᵇ to y ≈ᵇ to (x ⊕ᵃ y)
    ⊕-pres-≎ : ∀ {x y z} → x ≎ y → x ≎ z → x ≎ (y ⊕ᵃ z)
