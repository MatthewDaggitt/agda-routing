open import Data.Fin
open import Data.Fin.Subset
open import Data.Fin.Properties using (_≟_)
open import Data.Vec using ([]; _∷_; here; there)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (refl)

module RoutingLib.Data.Fin.Subset where

  _∈?_ : ∀ {n} i (xs : Subset n) → Dec (i ∈ xs)
  zero    ∈? (inside  ∷ _) = yes here
  zero    ∈? (outside ∷ _) = no λ()
  (suc l) ∈? (_ ∷ xs)      with l ∈? xs
  ... | yes l∈xs = yes (there l∈xs)
  ... | no  l∉xs = no λ{(there l∈xs) → l∉xs l∈xs}
