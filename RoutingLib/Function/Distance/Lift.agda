open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Relation.Binary using (Setoid)

open import RoutingLib.Data.Table using (Table; max)
import RoutingLib.Data.Table.IndexedTypes as IndexedType using (M)

module RoutingLib.Function.Distance.Lift {a ℓ n} (S : Fin n → Setoid a ℓ) where

  open IndexedType S
  
  module _ (i : Fin n) where

    open Setoid (S i) using () renaming (Carrier to Mᵢ) public
    
    
  maxLift : (∀ {i} → Mᵢ i → Mᵢ i → ℕ) → M → M → ℕ
  maxLift dᵢ x y = max 0 (λ i → dᵢ (x i) (y i))
