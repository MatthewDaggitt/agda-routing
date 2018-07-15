open import Algebra.FunctionProperties using (Op₂)
open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec
open import Data.Vec.Relation.Pointwise.Inductive
open import Function using (_∘_)

open import RoutingLib.Data.Vec

module RoutingLib.Data.Vec.Relation.Pointwise.Inductive where

module _ {a b} {A : Set a} {B : Set b} where

  tabulate⁺ : ∀ {p} (P : A → B → Set p)
              {n} {f : Fin n → A} {g : Fin n → B} →
              (∀ i → P (f i) (g i)) →
              Pointwise P (tabulate f) (tabulate g)
  tabulate⁺ P {zero}  Pfg = []
  tabulate⁺ P {suc n} Pfg = Pfg zero ∷ tabulate⁺ P (Pfg ∘ suc)
