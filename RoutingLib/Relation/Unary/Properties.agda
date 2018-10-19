open import Relation.Unary

module RoutingLib.Relation.Unary.Properties where

module _  {a p q} {A : Set a} {P : Pred A p} {Q : Pred A q} where

  ∀-⊆′ : P ⊆′ Q → Universal P → Universal Q
  ∀-⊆′ P⊆Q ∀P x = P⊆Q x (∀P x)

  ∀-⊆ : P ⊆ Q → Universal P → Universal Q
  ∀-⊆ P⊆Q ∀P x = P⊆Q (∀P x)
