open import Data.Unit using (tt)

open import RoutingLib.Relation.Unary.Indexed

module RoutingLib.Relation.Unary.Indexed.Properties where

Uᵢ-universal : ∀ {a i} {I : Set i} (Aᵢ : I → Set a) → Universalᵢ {Aᵢ = Aᵢ} Uᵢ
Uᵢ-universal Aᵢ x = tt
