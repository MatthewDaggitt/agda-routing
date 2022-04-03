open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Level using (Level)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Unary using (Pred; _⊆_; Decidable)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Routing.Basics.Path.Certified

module RoutingLib.Routing.Basics.Path.Certified.AllVertices {n : ℕ} where

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    P Q : Pred (Vertex n) ℓ
    p q : Path n
    
----------------------------------------------------------------------------
-- Datatypes

data Allᵥ (P : Pred (Vertex n) ℓ) : Path n → Set ℓ where
  []      : Allᵥ P []
  [_,_]∷_ : ∀ {i j p ij⇿p i∉p} → P i → P j → Allᵥ P p → Allᵥ P ((i , j) ∷ p ∣ ij⇿p ∣ i∉p)

----------------------------------------------------------------------------
-- Operations

mapᵥ : P ⊆ Q → Allᵥ P ⊆ Allᵥ Q
mapᵥ P⊆Q []                = []
mapᵥ P⊆Q ([ Pi , Pj ]∷ Pp) = [ (P⊆Q Pi) , (P⊆Q Pj) ]∷ (mapᵥ P⊆Q Pp)

----------------------------------------------------------------------------
-- Properties

Allᵥ-resp-≈ₚ : Allᵥ P p → p ≈ₚ q → Allᵥ P q
Allᵥ-resp-≈ₚ []                []           = []
Allᵥ-resp-≈ₚ ([ Pi , Pj ]∷ Pp) (refl ∷ p≈q) = [ Pi , Pj ]∷ Allᵥ-resp-≈ₚ Pp p≈q
