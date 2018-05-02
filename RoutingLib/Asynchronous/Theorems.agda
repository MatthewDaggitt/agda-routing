open import Relation.Binary using (Setoid)

open import RoutingLib.Asynchronous
open import RoutingLib.Data.Table using (Table)

module RoutingLib.Asynchronous.Theorems {a ℓ n} {S : Table (Setoid a ℓ) n}
                                        {P : Parallelisation S} where

  -- Export core publically
  
  open import RoutingLib.Asynchronous.Theorems.Core public

  -- Theorems
  
  totalACO⇒safe : ∀ {p} → TotalACO P p → IsAsynchronouslySafe P
  totalACO⇒safe = isAsynchronouslySafe
    where open import RoutingLib.Asynchronous.Theorems.UresinDubois1 P using (isAsynchronouslySafe)

  ultra⇒totalACO : UltrametricConditions P → TotalACO P _
  ultra⇒totalACO ultra = totalACO
    where open import RoutingLib.Asynchronous.Theorems.MetricToBox ultra using (totalACO)

  ultra⇒safe : UltrametricConditions P → IsAsynchronouslySafe P
  ultra⇒safe ultra = totalACO⇒safe (ultra⇒totalACO ultra)
