open import Data.Fin using (Fin; toℕ)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_)
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

open import RoutingLib.Data.Path.UncertifiedI
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.RoutingAlgebra

module RoutingLib.Routing.Algebra.PathAlgebra
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) where

--------------------------------------------------------------------------------
-- Algebras that represent path-vector protocols

open RawRoutingAlgebra algebra

record IsPathAlgebra : Set (a ⊔ b ⊔ ℓ) where
  no-eta-equality -- Needed due to bug #2732 in Agda

  field
    isRoutingAlgebra : IsRoutingAlgebra algebra

    path           : Route → Path
    path-cong      : path Preserves _≈_ ⟶ _≡_
    r≈0⇒path[r]≈[] : ∀ {r} → r ≈ 0# → path r ≡ valid []
    r≈∞⇒path[r]≈∅  : ∀ {r} → r ≈ ∞  → path r ≡ invalid
    path[r]≈∅⇒r≈∞  : ∀ {r} → path r ≡ invalid → r ≈ ∞
    path-reject    : ∀ {n} {i j : Fin n} {r p} (f : Step i j) → path r ≡ valid p →
                     (¬ (toℕ i , toℕ j) ⇿ᵥ p) ⊎ toℕ i ∈ᵥₚ p → f ▷ r ≈ ∞
    path-accept    : ∀ {n} {i j : Fin n} {r p} (f : Step i j) → path r ≡ valid p → f ▷ r ≉ ∞ →
                     path (f ▷ r) ≡ valid ((toℕ i , toℕ j) ∷ p)

  open IsRoutingAlgebra isRoutingAlgebra public
