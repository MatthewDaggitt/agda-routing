open import Level using () renaming (zero to lzero)
open import Data.Fin using (Fin)
open import Data.Fin.Subset using (_∈_; _∉_)
open import Data.Nat using (ℕ; zero; suc; s≤s; _<_; _≤_; _∸_; _≟_; _⊔_; _+_)
open import Data.Nat.Properties using (1+n≰n; ≤-refl; ≤+≢⇒<; <⇒≤; +-suc; ≤-trans; <-transʳ)
open import Data.List using (foldr; tabulate; applyUpTo)
open import Data.Product using (∃; _×_; _,_; proj₁)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst)
open import Relation.Nullary using (¬_; yes; no)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using (<-wellFounded)

open import RoutingLib.Data.Table using (max)
import RoutingLib.Data.List.Extrema.Nat as List

open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule

module RoutingLib.Iteration.Asynchronous.Dynamic.Schedule.Pseudoperiod {n} (𝓢 : Schedule n) where

open Schedule 𝓢

--------------------------------------------------------------------------------
-- Sub epochs --
--------------------------------------------------------------------------------
--
-- Periods of time within an epoch.
-- These are typically named η[s,e].

record IsSubEpoch (period : TimePeriod) : Set where
  constructor mkₛₑ
  open TimePeriod period
  field
    start≤end : start ≤ end
    ηₛ≡ηₑ     : η start ≡ η end

_++ₛₑ_ : ∀ {s m e} → IsSubEpoch [ s , m ] → IsSubEpoch [ m , e ] → IsSubEpoch [ s , e ]
(mkₛₑ s≤m ηₛ≡ηₘ) ++ₛₑ (mkₛₑ m≤e ηₘ≡ηₑ) = record
  { start≤end = ≤-trans s≤m m≤e
  ; ηₛ≡ηₑ     = trans ηₛ≡ηₘ ηₘ≡ηₑ
  } where open IsSubEpoch

--------------------------------------------------------------------------------
-- Activation periods --
--------------------------------------------------------------------------------
--
-- In activation period every participating node is activated at least once.
-- These are typically named α[s,e]

record _IsActiveIn_ (i : Fin n) (period : TimePeriod) : Set where
  constructor mkₐᵢ
  open TimePeriod period
  field
    ηₛ≡ηₑ         : η start ≡ η end
    α+            : 𝕋
    s<α+          : start < α+
    α+≤e          : α+ ≤ end
    i∈α+[i]       : i ∈ α α+

  η[s,e] : IsSubEpoch [ start , end ]
  η[s,e] = mkₛₑ (≤-trans (<⇒≤ s<α+) α+≤e) ηₛ≡ηₑ

record IsActivationPeriod (period : TimePeriod) : Set where
  constructor mkₐ
  open TimePeriod period
  field
    η[s,e]        : IsSubEpoch period
    isActivation  : ∀ {i} → i ∈ ρ start → i IsActiveIn period

  open IsSubEpoch η[s,e] public

  module _ {i} (i∈ρ : i ∈ ρ start) where
    open _IsActiveIn_ (isActivation i∈ρ) public hiding (ηₛ≡ηₑ; η[s,e])

--------------------------------------------------------------------------------
-- Expiry periods --
--------------------------------------------------------------------------------
--
-- After the end of an expiry period, there are no messages left in flight that
-- originate from before the start of the expiry period.
--
-- These are typically named β[s,e]

record IsExpiryPeriod (period : TimePeriod) : Set where
  constructor mkₑ
  open TimePeriod period
  field
    η[s,e]  : IsSubEpoch period
    expiryᵢ  : ∀ {i} → i ∈ ρ start → ∀ {t} → end ≤ t → ∀ j → start ≤ β t i j

  open IsSubEpoch η[s,e] public

--------------------------------------------------------------------------------
-- Pseudoperiod
--------------------------------------------------------------------------------
--
-- A time period that "emulates" one synchronous iteration. During a
-- pseudoperiod every node activates and then we wait until all data before
-- those activation points are flushed from the system.

record IsPseudoperiodic (period : TimePeriod) : Set₁ where
  open TimePeriod period
  field
    m      : 𝕋
    β[s,m] : IsExpiryPeriod     [ start , m   ]
    α[m,e] : IsActivationPeriod [ m     , end ]

  open IsExpiryPeriod β[s,m] public
    renaming (start≤end to start≤mid; ηₛ≡ηₑ to ηₛ≡ηₘ; η[s,e] to η[s,m])
  open IsActivationPeriod α[m,e] public
    renaming (start≤end to mid≤end;   ηₛ≡ηₑ to ηₘ≡ηₑ; η[s,e] to η[m,e])
  
  start≤end : start ≤ end
  start≤end = ≤-trans start≤mid mid≤end

  ηₛ≡ηₑ : η start ≡ η end
  ηₛ≡ηₑ = trans ηₛ≡ηₘ ηₘ≡ηₑ

  η[s,e] : IsSubEpoch [ start , end ]
  η[s,e] = mkₛₑ start≤end ηₛ≡ηₑ

--------------------------------------------------------------------------------
-- Multi-pseudoperiods
--------------------------------------------------------------------------------
--
-- A time period that contains k pseudoperiods

data IsMultiPseudoperiodic : ℕ → TimePeriod → Set₁ where
  none : ∀ {s}         → IsMultiPseudoperiodic 0 [ s , s ]
  next : ∀ {s} m {e k} → IsPseudoperiodic [ s , m ] → IsMultiPseudoperiodic k [ m , e ] → IsMultiPseudoperiodic (suc k) [ s , e ]

ηₛ≡ηₑ-mpp : ∀ {s e k} → IsMultiPseudoperiodic k [ s , e ] → η s ≡ η e
ηₛ≡ηₑ-mpp none            = refl
ηₛ≡ηₑ-mpp (next m pp mpp) = trans (IsPseudoperiodic.ηₛ≡ηₑ pp) (ηₛ≡ηₑ-mpp mpp)

s≤e-mpp : ∀ {s e k} → IsMultiPseudoperiodic k [ s , e ] → s ≤ e
s≤e-mpp none            = ≤-refl
s≤e-mpp (next m pp mpp) = ≤-trans (IsPseudoperiodic.start≤end pp) (s≤e-mpp mpp)



{-
-----------------
-- Activations --
-----------------

-- return the first time after t but before t + suc k that i is active
nextActive' : (t k : 𝕋) {i : I} → i ∈ α (t + suc k) → Acc _<_ k → 𝕋
nextActive' t zero    {i} _          _       = suc t
nextActive' t (suc k) {i} i∈α[t+1+K] (acc rs) with i ∈?α t
... | yes i∈α                         = t
... | no  i∉α rewrite +-suc t (suc k) = nextActive' (suc t) k i∈α[t+1+K] (rs k ≤-refl)

-- returns the first time after t in which that i is active
nextActive : 𝕋 → I → 𝕋
nextActive t i with nonstarvation t i
... | (K , i∈α[t+1+K]) = nextActive' t K i∈α[t+1+K] (<-wellFounded K)

-- returns the first time after t such that all nodes have activated since t
allActive : 𝕋 → 𝕋
allActive t = max t (nextActive t)

---------------
-- Data flow --
---------------

-- pointExpiryᵢⱼ returns a time such that i does not use data from j from time t

pointExpiryᵢⱼ : I → I → 𝕋 → 𝕋
pointExpiryᵢⱼ i j t = proj₁ (finite t i j)

-- expiryᵢⱼ returns a time such that i only uses data from j after time t

expiryᵢⱼ : 𝕋 → I → I → 𝕋
expiryᵢⱼ t i j = List.max t (applyUpTo (pointExpiryᵢⱼ i j) (suc t))

-- expiryᵢⱼ : 𝕋 → Fin n → Fin n → 𝕋
-- expiryᵢⱼ t i j = max {suc t} t (pointExpiryᵢⱼ i j)


-- expiryᵢ returns a time ≥ t such that i only ever uses data from after time t
expiryᵢ : 𝕋 → I → 𝕋
expiryᵢ t i = max t (expiryᵢⱼ t i)

-- expiry returns a time ≥ t such that all nodes only ever uses data from after time t
expiry : 𝕋 → 𝕋
expiry t = max t (expiryᵢ t)

-------------------
-- Pseudo-Cycles --
-------------------

-- Definition of φ
φ : ℕ → 𝕋
φ zero     = zero
φ (suc K)  = suc (expiry (allActive (φ K)))

-- Definition of τ
τ : ℕ → I → 𝕋
τ K i = nextActive (φ K) i
-}
