--------------------------------------------------------------------------------
-- Creating dynamic schedules from static schedules
--------------------------------------------------------------------------------

module RoutingLib.Iteration.Asynchronous.Dynamic.Schedule.FromStatic where

open import Data.Nat
open import Data.Fin.Subset using (⊤)
open import Function using (_∘_; const)
open import Relation.Binary.PropositionalEquality using (refl)

open import RoutingLib.Data.Fin.Subset using (Full)
open import RoutingLib.Data.Fin.Subset.Properties using (⊤-full)

open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule
open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule.Pseudoperiod
import RoutingLib.Iteration.Asynchronous.Static.Schedule.Pseudoperiod as Static

--------------------------------------------------------------------------------
-- Any static schedule can be converted to a dynamic schedule with a single
-- epoch

trivialEpochSchedule : ∀ n → EpochSchedule n
trivialEpochSchedule n = record
  { η      = const 0
  ; π      = const ⊤
  ; η-mono = const z≤n
  }

convert : ∀ {n} → StaticSchedule n → Schedule n
convert {n} static = record
  { staticSchedule = static
  ; epochSchedule  = trivialEpochSchedule n
  }

--------------------------------------------------------------------------------
-- Properties

module _ {n} (ψˢ : StaticSchedule n) where

  private
    ψᵈ : Schedule n
    ψᵈ = convert ψˢ

  convert-subEpoch : ∀ {s e} → s ≤ e → SubEpoch ψᵈ [ s , e ]
  convert-subEpoch s≤e = mkₛₑ s≤e refl

  convert-isActiveIn : ∀ {s e i} →
                       Static._IsActiveIn_ ψˢ i [ s , e ] →
                       _IsActiveIn_ ψᵈ i [ s , e ]
  convert-isActiveIn (Static.mkₐ α+ s<α+ α+≤e i∈α+[i]) =
    mkₐᵢ refl α+ s<α+ α+≤e i∈α+[i]

  convert-expiryPeriod : ∀ {s e i} → Static.MessagesTo_ExpireIn_ ψˢ i [ s , e ] →
                         MessagesTo_ExpireIn_ ψᵈ i ([ s , e ])
  convert-expiryPeriod (Static.mkₑ start≤end expiryᵢ) =
    mkₑ (convert-subEpoch start≤end) expiryᵢ

  convert-pseudoperiod : ∀ {s e} → Static.Pseudocycle ψˢ [ s , e ] →
                         Pseudocycle ψᵈ [ s , e ]
  convert-pseudoperiod pp = record
    { m          = m
    ; η[s,e]     = convert-subEpoch start≤end
    ; start≤midᵢ = start≤midᵢ
    ; midᵢ≤end   = midᵢ≤end
    ; β[s,m]     = convert-expiryPeriod ∘ β[s,m]
    ; α[m,e]     = λ {i} i∈ρₛ → convert-isActiveIn (α[m,e] i)
    } where open Static.Pseudocycle pp

  convert-multiPseudocycle : ∀ {s e k} → Static.MultiPseudocycle ψˢ k [ s , e ] →
                              MultiPseudocycle ψᵈ k [ s , e ]
  convert-multiPseudocycle Static.none            = none
  convert-multiPseudocycle (Static.next m pp mpp) =
    next m (convert-pseudoperiod pp) (convert-multiPseudocycle mpp)

  convert∈Full : ψᵈ satisfies Full
  convert∈Full t = ⊤-full
