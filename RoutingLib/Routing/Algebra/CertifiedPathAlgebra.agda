open import Data.Fin using (Fin; toℕ)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_)
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

open import RoutingLib.Data.Path.CertifiedI

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.RoutingAlgebra

module RoutingLib.Routing.Algebra.CertifiedPathAlgebra
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) where

open RawRoutingAlgebra algebra

--------------------------------------------------------------------------------
-- Algebras that represent path-vector protocols with nodes in network
-- and proofs of simple paths

record IsCertifiedPathAlgebra (n : ℕ) : Set (a ⊔ b ⊔ ℓ) where
  no-eta-equality -- Needed due to bug #2732 in Agda

  field
    isRoutingAlgebra : IsRoutingAlgebra algebra

    path           : Route → Path n
    path-cong      : path Preserves _≈_ ⟶ _≈ₚ_
    r≈0⇒path[r]≈[] : ∀ {r} → r ≈ 0# → path r ≈ₚ valid []
    r≈∞⇒path[r]≈∅  : ∀ {r} → r ≈ ∞  → path r ≈ₚ invalid
    path[r]≈∅⇒r≈∞  : ∀ {r} → path r ≈ₚ invalid → r ≈ ∞
    path-reject    : ∀ {i j : Fin n} {r p} (f : Step i j) → path r ≈ₚ valid p →
                     (¬ (i , j) ⇿ᵛ p) ⊎ i ∈ᵥₚ p → f ▷ r ≈ ∞
    path-accept    : ∀ {i j : Fin n} {r p} (f : Step i j) → path r ≈ₚ valid p → f ▷ r ≉ ∞ →
                     ∀ ij⇿p i∉p → path (f ▷ r) ≈ₚ valid ((i , j) ∷ p ∣ ij⇿p ∣ i∉p)

  open IsRoutingAlgebra isRoutingAlgebra public

  -- Functions

  size : Route → ℕ
  size r = length (path r)

  weight : AdjacencyMatrix algebra n → Path n → Route
  weight A invalid                       = ∞
  weight A (valid [])                    = 0#
  weight A (valid ((i , j) ∷ p ∣ _ ∣ _)) = A i j ▷ weight A (valid p)
