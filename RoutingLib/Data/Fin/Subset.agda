open import Data.Fin.Subset
open import Relation.Nullary using (¬_)

module RoutingLib.Data.Fin.Subset where

Full : ∀ {n} → Subset n → Set
Full p = ∀ i → i ∈ p

Nonfull : ∀ {n} → Subset n → Set
Nonfull p = ¬ (Full p)
