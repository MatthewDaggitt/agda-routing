open import Relation.Unary using (Pred)

open import RoutingLib.Data.Table

module RoutingLib.Data.Table.All where

  All : ∀ {a ℓ} {A : Set a} → Pred A ℓ → ∀ {n} → Pred (Table A n) ℓ
  All P t = ∀ i → P (t i)
