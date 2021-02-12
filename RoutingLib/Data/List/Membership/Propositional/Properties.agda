open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List.Base
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-allFin)
open import Data.Product using (_,_)

open import RoutingLib.Data.List using (allFinPairs)

module RoutingLib.Data.List.Membership.Propositional.Properties where

import Data.List.Membership.Propositional.Properties as GM

∈-allFinPairs⁺ : ∀ {n} i j → (i , j) ∈ allFinPairs n
∈-allFinPairs⁺ i j = GM.∈-cartesianProduct⁺ (∈-allFin i) (∈-allFin j)
