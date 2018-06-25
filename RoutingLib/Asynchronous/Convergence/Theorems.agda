open import Relation.Binary using (Setoid)

open import RoutingLib.Asynchronous
open import RoutingLib.Data.Table using (Table)

import RoutingLib.Asynchronous.Convergence.Proofs.UresinDubois1 as UresinDubois1
import RoutingLib.Asynchronous.Convergence.Proofs.Gurney6 as Gurney6

module RoutingLib.Asynchronous.Convergence.Theorems
  {a ℓ n} {S : Table (Setoid a ℓ) n}
  {P : Parallelisation S} where

  -- Export core publically
  open import RoutingLib.Asynchronous.Convergence.Conditions public

  -- Theorems
  
  totalACO⇒safe : ∀ {p} → TotalACO P p → IsAsynchronouslySafe P
  totalACO⇒safe = isAsynchronouslySafe
    where open UresinDubois1 P using (isAsynchronouslySafe)

  ultra⇒totalACO : UltrametricConditions P → TotalACO P _
  ultra⇒totalACO ultra = totalACO
    where open Gurney6 ultra using (totalACO)

  ultra⇒safe : UltrametricConditions P → IsAsynchronouslySafe P
  ultra⇒safe ultra = totalACO⇒safe (ultra⇒totalACO ultra)
