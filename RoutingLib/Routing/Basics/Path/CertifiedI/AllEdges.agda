open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Data.Maybe.Relation.Unary.All as MaybeAll using (All)
open import Function.Base using (_∘_)
open import Level using (Level)
open import Relation.Unary using (Pred; Decidable; _⊆_)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Routing.Basics.Path.CertifiedI
import RoutingLib.Routing.Basics.Path.Certified.AllEdges as NEP

module RoutingLib.Routing.Basics.Path.CertifiedI.AllEdges {n : ℕ} where

private
  variable
    ℓ : Level
    P Q : Pred (Edge n) ℓ
    p q : Path n
    
----------------------------------------------------------------------------
-- Datatypes

open NEP public using ([]; _∷_)

Allₑ : (P : Pred (Edge n) ℓ) → Path n → Set ℓ
Allₑ P = All (NEP.Allₑ P)

pattern trivial = valid []

----------------------------------------------------------------------------
-- Operations

allₑ? : Decidable P → Decidable (Allₑ P)
allₑ? = MaybeAll.dec ∘ NEP.allₑ?

----------------------------------------------------------------------------
-- Properties

Allₑ-resp-≈ₚ : ∀ {p q} → Allₑ P p → p ≈ₚ q → Allₑ P q
Allₑ-resp-≈ₚ invalid   invalid     = invalid
Allₑ-resp-≈ₚ (valid p) (valid p≈q) = valid (NEP.Allₑ-resp-≈ₚ p p≈q)
