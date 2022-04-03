open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Data.Maybe.Relation.Unary.All as MaybeAll using (All)
open import Function.Base using (_∘_)
open import Level using (Level)
open import Relation.Unary using (Pred; Decidable; _⊆_)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Routing.Basics.Path.CertifiedI
import RoutingLib.Routing.Basics.Path.Certified.AllVertices as NEP

module RoutingLib.Routing.Basics.Path.CertifiedI.AllVertices {n : ℕ} where

private
  variable
    ℓ : Level
    P Q : Pred (Vertex n) ℓ
    p q : Path n
    
----------------------------------------------------------------------------
-- Datatypes

open NEP public
  using ([]; [_,_]∷_)

Allᵥ : (P : Pred (Vertex n) ℓ) → Path n → Set ℓ
Allᵥ P = All (NEP.Allᵥ P)

pattern trivial = valid []

----------------------------------------------------------------------------
-- Operations

mapᵥ : P ⊆ Q → Allᵥ P ⊆ Allᵥ Q
mapᵥ = MaybeAll.map ∘ NEP.mapᵥ

----------------------------------------------------------------------------
-- Properties

Allᵥ-resp-≈ₚ : Allᵥ P p → p ≈ₚ q → Allᵥ P q
Allᵥ-resp-≈ₚ invalid    invalid    = invalid
Allᵥ-resp-≈ₚ (valid p) (valid p≈q) = valid (NEP.Allᵥ-resp-≈ₚ p p≈q)
