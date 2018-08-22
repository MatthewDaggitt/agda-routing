open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Unary using (Pred; _⊆_; Decidable)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Data.VertexPath.NonEmpty
open import RoutingLib.Data.VertexPath.NonEmpty.Relation.Equality

module RoutingLib.Data.VertexPath.NonEmpty.All where

  ----------------------------------------------------------------------------
  -- Datatypes

  data All {a} (P : Pred ℕ a) : Pathⁿᵗ → Set a where
    [_] : ∀ {i} → P i → All P [ i ]
    _∷_ : ∀ {i p i∉p} → P i → All P p → All P (i ∷ p ∣ i∉p)

  ----------------------------------------------------------------------------
  -- Operations

  map : ∀ {a b} {P : Pred ℕ a} {Q : Pred ℕ b} →
        P ⊆ Q → All P ⊆ All Q
  map P⊆Q [ Pi ]    = [ P⊆Q Pi ]
  map P⊆Q (Pi ∷ Pp) = (P⊆Q Pi) ∷ (map P⊆Q Pp)

  ----------------------------------------------------------------------------
  -- Properties

  module _ {a} {P : Pred ℕ a} where

    All-resp-≈ₚ : ∀ {p q} → All P p → p ≈ₚ q → All P q
    All-resp-≈ₚ [ Pi ]    [ refl ]     = [ Pi ]
    All-resp-≈ₚ (Pi ∷ Pp) (refl ∷ p≈q) = Pi ∷ All-resp-≈ₚ Pp p≈q
