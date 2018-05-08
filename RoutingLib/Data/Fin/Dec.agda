
open import Data.Fin
open import Data.Product using (∃; ∄; _,_)
open import Data.Nat
open import Function using (_∘_)
open import Relation.Unary using (Decidable)
open import Relation.Nullary using (Dec; yes; no)

module RoutingLib.Data.Fin.Dec where

any? : ∀ {n p} {P : Fin n → Set p} →
       Decidable P → Dec (∃ P)
any? {zero}      dec = no λ { (() , _) }
any? {suc n} {P} dec with dec zero | any? (dec ∘ suc)
...                  | yes p | _            = yes (_ , p)
...                  | _     | yes (_ , p') = yes (_ , p')
...                  | no ¬p | no ¬p'       = no λ
  { (zero  , p)  → ¬p p
  ; (suc f , p') → ¬p' (f , p')
  }
