open import Data.Fin using (zero; suc)
open import Data.List as List
open import Data.List.Relation.Unary.Linked
open import Data.Maybe
open import Relation.Binary
open import Level using (Level)

open import Data.Maybe.Relation.Binary.Connected

module RoutingLib.Data.List.Relation.Unary.Linked.Properties where

private
  variable
    a ℓ : Level
    A : Set a
    R : Rel A ℓ
    v : A
    xs : List A
    
lookup-Linked : Transitive R → Linked R xs →
                Connected R (just v) (List.head xs) →
                ∀ i → R v (lookup xs i)
lookup-Linked trans [-]       (just Rvx) zero    = Rvx
lookup-Linked trans (x ∷ xs↗) (just Rvx) zero    = Rvx
lookup-Linked trans (x ∷ xs↗) (just Rvx) (suc i) = lookup-Linked trans xs↗ (just (trans Rvx x)) i
