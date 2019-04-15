open import Relation.Unary using (Pred)
open import Data.Product using (∃)

open import RoutingLib.Data.Table

module RoutingLib.Data.Table.Relation.Unary.Any where


  Any : ∀ {a ℓ} {A : Set a} → Pred A ℓ → ∀ {n} → Pred (Table A n) ℓ
  Any P t = ∃ λ i → P (t i)
