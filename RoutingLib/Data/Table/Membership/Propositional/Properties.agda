open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (⊔-sel)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl; setoid)

open import RoutingLib.Data.Nat.Properties using (ℕₛ)
open import RoutingLib.Data.Table
open import RoutingLib.Data.Table.Membership.Properties
open import RoutingLib.Data.Table.Membership.Propositional

module RoutingLib.Data.Table.Membership.Propositional.Properties where

  max+∈t : ∀ {n} (t : Table ℕ (suc n)) → max+ t ∈ t
  max+∈t t = sel⇒foldr+∈t ℕₛ ⊔-sel t
