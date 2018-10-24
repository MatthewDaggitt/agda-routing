open import Algebra.FunctionProperties using (Commutative)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel; Total)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

module RoutingLib.Algebra.FunctionProperties.Consequences.Propositional where

wlog : ∀ {a p} {A : Set a} {P : Pred A p}
       {f} → Commutative _≡_ f →
       ∀ {r} {_∼_ : Rel _ r} → Total _∼_ →
       (∀ {a b} → a ∼ b → P (f a b)) →
       ∀ a b → P (f a b)
wlog {P = P} comm total R⇒Pf a b with total a b
... | inj₁ a∼b = R⇒Pf a∼b
... | inj₂ b∼a = subst P (comm b a) (R⇒Pf b∼a)
