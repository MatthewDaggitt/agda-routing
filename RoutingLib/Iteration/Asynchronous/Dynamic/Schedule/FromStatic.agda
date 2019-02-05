--------------------------------------------------------------------------------
-- Creating dynamic schedules from static schedules
--------------------------------------------------------------------------------

module RoutingLib.Iteration.Asynchronous.Dynamic.Schedule.FromStatic where

open import Data.Nat
open import Data.Fin.Subset using (⊤)
open import Function using (const)
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
  convert-isActiveIn (Static.mkₐᵢ α+ s<α+ α+≤e i∈α+[i]) =
    mkₐᵢ refl α+ s<α+ α+≤e i∈α+[i]

  convert-activationPeriod : ∀ {s e} → Static.ActivationPeriod ψˢ [ s , e ] →
                             ActivationPeriod ψᵈ [ s , e ]
  convert-activationPeriod (Static.mkₐ start≤end isActivation) =
    mkₐ (convert-subEpoch start≤end) (λ _ → convert-isActiveIn (isActivation _))

  convert-expiryPeriod : ∀ {s e} → Static.ExpiryPeriod ψˢ [ s , e ] →
                             ExpiryPeriod ψᵈ [ s , e ]
  convert-expiryPeriod (Static.mkₑ start≤end expiryᵢ) =
    mkₑ (convert-subEpoch start≤end) (λ _ e<t j → expiryᵢ _ j e<t)

  convert-pseudoperiod : ∀ {s e} → Static.Pseudoperiod ψˢ [ s , e ] →
                         Pseudoperiod ψᵈ [ s , e ]
  convert-pseudoperiod pp = record
    { m      = m
    ; β[s,m] = convert-expiryPeriod β[s,m]
    ; α[m,e] = convert-activationPeriod α[m,e]
    } where open Static.Pseudoperiod pp

  convert-multiPseudoperiod : ∀ {s e k} → Static.MultiPseudoperiod ψˢ k [ s , e ] →
                              MultiPseudoperiod ψᵈ k [ s , e ]
  convert-multiPseudoperiod Static.none            = none
  convert-multiPseudoperiod (Static.next m pp mpp) =
    next m (convert-pseudoperiod pp) (convert-multiPseudoperiod mpp)

  convert∈Full : ψᵈ satisfies Full
  convert∈Full t = ⊤-full
