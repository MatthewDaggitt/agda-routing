open import Relation.Unary

module RoutingLib.Relation.Unary where

  _Preserves_ : ∀ {a p} {A : Set a} → (A → A) → Pred A p → Set _
  f Preserves P = ∀ {a} → P a → P (f a)

  _Forces_ : ∀ {a p} {A : Set a} → (A → A) → Pred A p → Set _
  f Forces P = ∀ {a} → P (f a) → P a
