open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Relation.Unary using (Pred; Decidable; _⊆_)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Routing.Basics.Path.CertifiedI
import RoutingLib.Routing.Basics.Path.Certified.All as NEP

module RoutingLib.Routing.Basics.Path.CertifiedI.All {n : ℕ} where

----------------------------------------------------------------------------
-- Datatypes

open NEP public using ([]; _∷_; [_,_]∷_)

data Allᵥ {a} (P : Pred (Vertex n) a) : Path n → Set a where
  invalid : Allᵥ P invalid
  valid   : ∀ {p} → NEP.Allᵥ P p → Allᵥ P (valid p)

data Allₑ {a} (P : Pred (Edge n) a) : Path n → Set a where
  invalid : Allₑ P invalid
  valid   : ∀ {p} → NEP.Allₑ P p → Allₑ P (valid p)

pattern trivial = valid []

----------------------------------------------------------------------------
-- Operations

module _ {a b} {P : Pred (Vertex n) a} {Q : Pred (Vertex n) b} where

  mapᵥ : P ⊆ Q → Allᵥ P ⊆ Allᵥ Q
  mapᵥ P⊆Q invalid   = invalid
  mapᵥ P⊆Q (valid x) = valid (NEP.mapᵥ P⊆Q x)

module _ {a} {P : Pred (Edge n) a} where

  allₑ? : Decidable P → Decidable (Allₑ P)
  allₑ? P? invalid   = yes invalid
  allₑ? P? (valid x) with NEP.allₑ? P? x
  ... | yes px = yes (valid px)
  ... | no ¬px = no λ {(valid px) → ¬px px}

----------------------------------------------------------------------------
-- Properties

module _ {a} {P : Pred (Fin n) a} where

  Allᵥ-resp-≈ₚ : ∀ {p q} → Allᵥ P p → p ≈ₚ q → Allᵥ P q
  Allᵥ-resp-≈ₚ invalid    invalid    = invalid
  Allᵥ-resp-≈ₚ (valid p) (valid p≈q) = valid (NEP.Allᵥ-resp-≈ₚ p p≈q)

module _ {a} {P : Pred (Fin n × Fin n) a} where

  Allₑ-resp-≈ₚ : ∀ {p q} → Allₑ P p → p ≈ₚ q → Allₑ P q
  Allₑ-resp-≈ₚ invalid   invalid     = invalid
  Allₑ-resp-≈ₚ (valid p) (valid p≈q) = valid (NEP.Allₑ-resp-≈ₚ p p≈q)
