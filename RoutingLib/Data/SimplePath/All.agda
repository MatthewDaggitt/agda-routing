open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Relation.Unary using (Pred)

open import RoutingLib.Data.SimplePath
open import RoutingLib.Data.SimplePath.Relation.Equality

import RoutingLib.Data.SimplePath.NonEmpty.All as NEP

module RoutingLib.Data.SimplePath.All {n : ℕ} where

  ----------------------------------------------------------------------------
  -- Datatypes
   
  open NEP public using ([]; [_,_]∷_)
  
  data All {a} (P : Pred (Fin n) a) : SimplePath n → Set a where
    invalid : All P invalid
    valid   : ∀ {p} → NEP.All P p → All P (valid p)

  ----------------------------------------------------------------------------
  -- Properties
    
  module _ {a} {P : Pred (Fin n) a} where
  
    All-resp-≈ₚ : ∀ {p q} → All P p → p ≈ₚ q → All P q
    All-resp-≈ₚ invalid    invalid     = invalid
    All-resp-≈ₚ (valid Pp) (valid p≈q) = valid (NEP.All-resp-≈ₚ Pp p≈q)
