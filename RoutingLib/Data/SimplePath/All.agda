open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Relation.Unary using (Pred; Decidable; _⊆_)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Data.SimplePath
open import RoutingLib.Data.SimplePath.Relation.Equality

import RoutingLib.Data.SimplePath.NonEmpty.All as NEP

module RoutingLib.Data.SimplePath.All {n : ℕ} where

  ----------------------------------------------------------------------------
  -- Datatypes
   
  open NEP public using ([]; _∷_; [_,_]∷_)
  
  data Allₙ {a} (P : Pred (Fin n) a) : SimplePath n → Set a where
    invalid : Allₙ P invalid
    valid   : ∀ {p} → NEP.Allₙ P p → Allₙ P (valid p)

  data Allₑ {a} (P : Pred (Fin n × Fin n) a) : SimplePath n → Set a where
    invalid : Allₑ P invalid
    valid   : ∀ {p} → NEP.Allₑ P p → Allₑ P (valid p)
    
  ----------------------------------------------------------------------------
  -- Operations

  mapₙ : ∀ {a b} {P : Pred (Fin n) a} {Q : Pred (Fin n) b} →
        P ⊆ Q → Allₙ P ⊆ Allₙ Q
  mapₙ P⊆Q invalid   = invalid
  mapₙ P⊆Q (valid x) = valid (NEP.mapₙ P⊆Q x)

  allₑ? : ∀ {a} {P : Pred (Fin n × Fin n) a} → Decidable P → Decidable (Allₑ P)
  allₑ? P? invalid   = yes invalid
  allₑ? P? (valid x) with NEP.allₑ? P? x
  ... | yes px = yes (valid px)
  ... | no ¬px = no λ {(valid px) → ¬px px}
  
  ----------------------------------------------------------------------------
  -- Properties
    
  module _ {a} {P : Pred (Fin n) a} where
  
    Allₙ-resp-≈ₚ : ∀ {p q} → Allₙ P p → p ≈ₚ q → Allₙ P q
    Allₙ-resp-≈ₚ invalid    invalid     = invalid
    Allₙ-resp-≈ₚ (valid p) (valid p≈q) = valid (NEP.Allₙ-resp-≈ₚ p p≈q)

  module _ {a} {P : Pred (Fin n × Fin n) a} where
  
    Allₑ-resp-≈ₚ : ∀ {p q} → Allₑ P p → p ≈ₚ q → Allₑ P q
    Allₑ-resp-≈ₚ invalid   invalid     = invalid
    Allₑ-resp-≈ₚ (valid p) (valid p≈q) = valid (NEP.Allₑ-resp-≈ₚ p p≈q)
