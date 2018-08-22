open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Relation.Unary using (Pred; Decidable; _⊆_)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Data.Path
open import RoutingLib.Data.Path.Relation.Equality

import RoutingLib.Data.Path.NonEmpty.All as NEP

module RoutingLib.Data.Path.All where

  ----------------------------------------------------------------------------
  -- Datatypes

  open NEP public using ([]; _∷_; [_,_]∷_)

  data Allₙ {a} (P : Pred ℕ a) : Path → Set a where
    invalid : Allₙ P invalid
    valid   : ∀ {p} → NEP.Allₙ P p → Allₙ P (valid p)

  data Allₑ {a} (P : Pred (ℕ × ℕ) a) : Path → Set a where
    invalid : Allₑ P invalid
    valid   : ∀ {p} → NEP.Allₑ P p → Allₑ P (valid p)

  ----------------------------------------------------------------------------
  -- Operations

  mapₙ : ∀ {a b} {P : Pred ℕ a} {Q : Pred ℕ b} →
        P ⊆ Q → Allₙ P ⊆ Allₙ Q
  mapₙ P⊆Q invalid   = invalid
  mapₙ P⊆Q (valid x) = valid (NEP.mapₙ P⊆Q x)

  allₑ? : ∀ {a} {P : Pred (ℕ × ℕ) a} → Decidable P → Decidable (Allₑ P)
  allₑ? P? invalid   = yes invalid
  allₑ? P? (valid x) with NEP.allₑ? P? x
  ... | yes px = yes (valid px)
  ... | no ¬px = no λ {(valid px) → ¬px px}

  ----------------------------------------------------------------------------
  -- Properties

  module _ {a} {P : Pred ℕ a} where

    Allₙ-resp-≈ₚ : ∀ {p q} → Allₙ P p → p ≈ₚ q → Allₙ P q
    Allₙ-resp-≈ₚ invalid    invalid    = invalid
    Allₙ-resp-≈ₚ (valid p) (valid p≈q) = valid (NEP.Allₙ-resp-≈ₚ p p≈q)

  module _ {a} {P : Pred (ℕ × ℕ) a} where

    Allₑ-resp-≈ₚ : ∀ {p q} → Allₑ P p → p ≈ₚ q → Allₑ P q
    Allₑ-resp-≈ₚ invalid   invalid     = invalid
    Allₑ-resp-≈ₚ (valid p) (valid p≈q) = valid (NEP.Allₑ-resp-≈ₚ p p≈q)