open import Data.Fin using (Fin)
open import Data.Product using (∃; _,_)
open import Function.Equality using (_⟨$⟩_)
open import Function.Injection using (_↣_; Injection)
open import Relation.Unary
open import Relation.Binary using (Setoid)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Function.Bijection using (_⤖_)

module RoutingLib.Relation.Unary where

_Preserves_ : ∀ {a p} {A : Set a} → (A → A) → Pred A p → Set _
f Preserves P = ∀ {a} → P a → P (f a)

_Forces_ : ∀ {a p} {A : Set a} → (A → A) → Pred A p → Set _
f Forces P = ∀ {a} → P (f a) → P a




{-
open Injection

module _ {a b p q} {A : Set a} {B : Set b} {P : Pred A p} {Q : Pred B q} where

  
  via-injection : A ↣ B → Decidable Q → Decidable P
  via-injection inj Q? x with Q? (to inj ⟨$⟩ x) -- ? -- (to inj ⟨$⟩ x) (to inj ⟨$⟩ y)
  ... | yes Q[fx] = yes {!!} --yes (Injection.injective inj injx≈injy)
  ... | no ¬Q[fx] = no (λ Px → ¬Q[fx] {!!}) --no (λ x≈y → injx≉injy (Π.cong (to inj) x≈y))
-}






Finite : ∀ {a p} {A : Set a} → Pred A p → Set _
Finite P = ∃ λ n → ∃ P ⤖ Fin n

{-
Finite-dec : ∀ {a p} {A : Set a} {P : Pred A p} → Finite P → Decidable P
Finite-dec {P = P} (n , inj) x = {!!}
  where open Injection inj
-}
