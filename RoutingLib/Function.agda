open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃; _×_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

module RoutingLib.Function where

-- Double composition

_∘₂_ : ∀ {a b c d} → {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
       (f : C → D) → (g : A → B → C) → (A → B → D)
f ∘₂ g = λ x y → f (g x y)
