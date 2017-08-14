open import Relation.Unary
open import Relation.Nullary using (¬_; yes; no)
open import Function using (_∘_)

module RoutingLib.Relation.Unary.Consequences where

  P?⇒¬P? : ∀ {a p} {A : Set a} {P : Pred A p} → Decidable P → Decidable (¬_ ∘ P)
  P?⇒¬P? P? x with P? x
  ... | yes Px = no (λ ¬Px → ¬Px Px)
  ... | no ¬Px = yes ¬Px
