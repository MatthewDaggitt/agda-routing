open import Data.Sum
open import Data.Product using (_,_)
open import Data.Fin using (toℕ)

open import Level using (suc; _⊔_)
open import Relation.Binary
open import Relation.Nullary using (¬_)

open import RoutingLib.Data.Path.EdgePath using (Path; valid; invalid)
open import RoutingLib.Data.Path.EdgePath.NonEmpty using (_⇿_; _∈_; []; _∷_∣_∣_)
open import RoutingLib.Data.Path.EdgePath.Relation.Equality 
open import RoutingLib.Data.Matrix using (SquareMatrix)

open import RoutingLib.Routing.Algebra


module RoutingLib.Routing.Alt where

record RawPathAlgebra2 a b ℓ n : Set (suc (a ⊔ b ⊔ ℓ)) where

  field
    rawRoutingAlgebra : RawRoutingAlgebra a b ℓ

  open RawRoutingAlgebra rawRoutingAlgebra public

  field
    A        : SquareMatrix Step n
    path     : Route → Path

--------------------------------------------------------------------------------
-- Path algebra

record IsPathAlgebra2 {a b ℓ n} (algebra : RawPathAlgebra2 a b ℓ n) : Set (a ⊔ b ⊔ ℓ) where

  open RawPathAlgebra2 algebra

  field
    isRoutingAlgebra : IsRoutingAlgebra rawRoutingAlgebra

    path-cong      : path Preserves _≈_ ⟶ _≈ₚ_
    r≈0⇒path[r]≈[] : ∀ {r} → r ≈ 0# → path r ≈ₚ valid []
    r≈∞⇒path[r]≈∅  : ∀ {r} → r ≈ ∞ → path r ≈ₚ invalid
    path[r]≈∅⇒r≈∞  : ∀ {r} → path r ≈ₚ invalid  → r ≈ ∞
    path-reject    : ∀ {i j r p} → path r ≈ₚ valid p → (¬ (toℕ i , toℕ j) ⇿ p) ⊎ (toℕ i ∈ p) →
                     (A i j ▷ r) ≈ ∞
    path-accept    : ∀ {i j r p} → path r ≈ₚ valid p → ¬ ((A i j ▷ r) ≈ ∞) →
                       ∀ ij⇿p i∉p → path (A i j ▷ r) ≈ₚ valid ((toℕ i , toℕ j) ∷ p ∣ ij⇿p ∣ i∉p)

  open IsRoutingAlgebra isRoutingAlgebra public

record PathAlgebra2 a b ℓ n : Set (suc (a ⊔ b ⊔ ℓ)) where

  field
    rawPathAlgebra : RawPathAlgebra2 a b ℓ n
    isPathAlgebra  : IsPathAlgebra2 rawPathAlgebra

  open RawPathAlgebra2 rawPathAlgebra public
  open IsPathAlgebra2 isPathAlgebra public

  routingAlgebra : RoutingAlgebra a b ℓ
  routingAlgebra = record
    { isRoutingAlgebra = isRoutingAlgebra
    }




------------------------------------------
-- Conversion

module _ {a b ℓ n} (alg : PathAlgebra2 a b ℓ n) where

  open PathAlgebra2 alg

  rpa : RawPathAlgebra a b ℓ n
  rpa = record
    { rawRoutingAlgebra = rawRoutingAlgebra
    ; A                 = A
    ; path              = {!!}
    }

  ipa : IsPathAlgebra rpa
  ipa = record
    { isRoutingAlgebra = isRoutingAlgebra
    ; path-cong  = {!!}
    ; r≈0⇒path[r]≈[] = {!!}
    ; r≈∞⇒path[r]≈∅ = {!!}
    ; path[r]≈∅⇒r≈∞ = {!!}
    ; path-reject = {!!}
    ; path-accept = {!!}
    }

  pa : PathAlgebra a b ℓ n
  pa = record
    { rawPathAlgebra = rpa
    ; isPathAlgebra  = ipa
    }
