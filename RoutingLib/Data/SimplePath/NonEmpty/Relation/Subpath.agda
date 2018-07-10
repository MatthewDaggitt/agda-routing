open import Data.Nat using (ℕ)
open import Level using () renaming (zero to ℓ₀)
open import Relation.Binary

open import RoutingLib.Data.SimplePath.NonEmpty
open import RoutingLib.Data.SimplePath.NonEmpty.Relation.Equality

module RoutingLib.Data.SimplePath.NonEmpty.Relation.Subpath {n : ℕ} where

  infix 4 _⊆ₚ_

  data _⊆ₚ_ : Rel (SimplePathⁿᵗ n) ℓ₀ where
    refl : ∀ {p q}           → p ≈ₚ q → p ⊆ₚ q
    drop : ∀ {p q e e⇿q e∉q} → p ⊆ₚ q → p ⊆ₚ (e ∷ q ∣ e⇿q ∣ e∉q)

  ----------------
  -- Properties

  abstract

    ⊆ₚ-cong : ∀ {p q r s : SimplePathⁿᵗ n} →
              p ≈ₚ q → r ≈ₚ s → p ⊆ₚ r → q ⊆ₚ s
    ⊆ₚ-cong p≈q r≈s       (refl p≈r) = refl (≈ₚ-trans (≈ₚ-sym p≈q) (≈ₚ-trans p≈r r≈s))
    ⊆ₚ-cong p≈q (_ ∷ r≈s) (drop p⊆r) = drop (⊆ₚ-cong p≈q r≈s p⊆r)

    ⊆ₚ-reflexive : ∀ {p q : SimplePathⁿᵗ n} → p ≈ₚ q → p ⊆ₚ q
    ⊆ₚ-reflexive p≈q = refl p≈q

    ⊆ₚ-trans : Transitive _⊆ₚ_
    ⊆ₚ-trans p⊆q (refl q≈r) = ⊆ₚ-cong ≈ₚ-refl q≈r p⊆q
    ⊆ₚ-trans p⊆q (drop q⊆r) = drop (⊆ₚ-trans p⊆q q⊆r)
