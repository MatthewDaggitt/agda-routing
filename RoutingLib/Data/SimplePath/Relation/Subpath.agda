open import Data.Nat using (ℕ)
open import Level using () renaming (zero to ℓ₀)
open import Relation.Binary

open import RoutingLib.Data.SimplePath
open import RoutingLib.Data.SimplePath.Relation.Equality
import RoutingLib.Data.SimplePath.NonEmpty.Relation.Subpath as NE

module RoutingLib.Data.SimplePath.Relation.Subpath {n : ℕ} where

  ------------------------------------------------------------------------------
  -- Relations

  data _⊆ₚ_ : Rel (SimplePath n) ℓ₀ where
    invalid : invalid ⊆ₚ invalid
    valid   : ∀ {p q} → p NE.⊆ₚ q → valid p ⊆ₚ valid q

  ------------------------------------------------------------------------------
  -- Properties

  abstract

    ⊆ₚ-reflexive : _≈ₚ_ ⇒ _⊆ₚ_
    ⊆ₚ-reflexive invalid     = invalid
    ⊆ₚ-reflexive (valid p≈q) = valid (NE.refl p≈q)

    ⊆ₚ-trans : Transitive _⊆ₚ_
    ⊆ₚ-trans invalid     invalid     = invalid
    ⊆ₚ-trans (valid p⊆q) (valid q⊆r) = valid (NE.⊆ₚ-trans p⊆q q⊆r)
