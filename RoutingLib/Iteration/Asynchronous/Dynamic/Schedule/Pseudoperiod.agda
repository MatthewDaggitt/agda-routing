--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module defines what it means for a period of time to be a pseudoperiod
-- with respect to some schedule. As is shown by the proofs in the module
-- `RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.ACOImpliesConvergent`
-- during a pseudoperiod the asynchronous iteration will make at least as much
-- progress towards the fixed point as a single synchronous iteration.
--------------------------------------------------------------------------------

open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule

module RoutingLib.Iteration.Asynchronous.Dynamic.Schedule.Pseudoperiod
  {n} (ψ : Schedule n) where

open import Level using () renaming (zero to lzero)
open import Data.Fin using (Fin)
open import Data.Fin.Subset using (_∈_; _∉_)
open import Data.Nat using (ℕ; zero; suc; s≤s; _<_; _≤_; _∸_; _≟_; _⊔_; _+_)
open import Data.Nat.Properties
open import Data.List using (foldr; tabulate; applyUpTo)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; subst)
open import Relation.Nullary using (¬_; yes; no)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using (<-wellFounded)

open import RoutingLib.Data.Table using (max)
import RoutingLib.Data.List.Extrema.Nat as List

open Schedule ψ

--------------------------------------------------------------------------------
-- Sub epochs --
--------------------------------------------------------------------------------
-- Periods of time within an epoch.
--
-- These are typically named η[s,e].

record SubEpoch (period : TimePeriod) : Set where
  constructor mkₛₑ
  open TimePeriod period
  field
    start≤end : start ≤ end
    ηₛ≡ηₑ     : η start ≡ η end

_++ₛₑ_ : ∀ {s m e} → SubEpoch [ s , m ] → SubEpoch [ m , e ] → SubEpoch [ s , e ]
(mkₛₑ s≤m ηₛ≡ηₘ) ++ₛₑ (mkₛₑ m≤e ηₘ≡ηₑ) = record
  { start≤end = ≤-trans s≤m m≤e
  ; ηₛ≡ηₑ     = trans ηₛ≡ηₘ ηₘ≡ηₑ
  } where open SubEpoch

η-trivial : ∀ t → SubEpoch [ t , t ]
η-trivial t = mkₛₑ ≤-refl refl

ηₛₑ-inRangeₛ : ∀ {s m e} → SubEpoch [ s , e ] → m ∈ₜ [ s , e ] → SubEpoch [ s , m ]
ηₛₑ-inRangeₛ (mkₛₑ _ ηₛ≡ηₑ) m∈[s,e] = mkₛₑ (proj₁ m∈[s,e]) (η-inRangeₛ ηₛ≡ηₑ m∈[s,e])

ηₛₑ-inRangeₑ : ∀ {s m e} → SubEpoch [ s , e ] → m ∈ₜ [ s , e ] → SubEpoch [ m , e ]
ηₛₑ-inRangeₑ (mkₛₑ _ ηₛ≡ηₑ) m∈[s,e] = mkₛₑ (proj₂ m∈[s,e]) (η-inRangeₑ ηₛ≡ηₑ m∈[s,e])

--------------------------------------------------------------------------------
-- Activation periods --
--------------------------------------------------------------------------------
-- In activation period every participating node is activated at least once.
--
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

  η[s,e] : SubEpoch [ start , end ]
  η[s,e] = mkₛₑ (≤-trans (<⇒≤ s<α+) α+≤e) ηₛ≡ηₑ

--------------------------------------------------------------------------------
-- Expiry periods --
--------------------------------------------------------------------------------
-- After the end of an expiry period, there are no messages left in flight that
-- originate from before the start of the expiry period.
--
-- These are typically named β[s,e]

record MessagesTo_ExpireIn_ (i : Fin n) (period : TimePeriod) : Set where
  constructor mkₑ
  open TimePeriod period
  field
    η[s,e]  : SubEpoch period
    expiryᵢ : ∀ {t} → end < t → ∀ j → start ≤ β t i j

  open SubEpoch η[s,e] public

extendExpiry : ∀ {a s e z i} → SubEpoch [ a , s ] → SubEpoch [ e , z ] →
               MessagesTo i ExpireIn [ s , e ] →
               MessagesTo i ExpireIn [ a , z ]
extendExpiry η[a,s]@(mkₛₑ a≤s _) η[e,z]@(mkₛₑ e≤z _) (mkₑ η[s,e] expiryᵢ) =
  mkₑ ((η[a,s] ++ₛₑ η[s,e]) ++ₛₑ η[e,z]) (λ z<t → ≤-trans a≤s ∘ expiryᵢ (<-transʳ e≤z z<t))

--------------------------------------------------------------------------------
-- Pseudocycle
--------------------------------------------------------------------------------
-- A time period that "emulates" one synchronous iteration. During a
-- pseudocycle every node activates and then we wait until all data before
-- those activation points are flushed from the system.

record Pseudocycle (period : TimePeriod) : Set₁ where
  open TimePeriod period
  field
    m          : Fin n → 𝕋
    η[s,e]     : SubEpoch [ start , end ]
    start≤midᵢ : ∀ i → start ≤ m i
    midᵢ≤end   : ∀ i → m i ≤ end
    
    β[s,m]     : ∀ {i} (i∈ρₛ : i ∈ ρ start) → MessagesTo i ExpireIn [ start , m i ]
    α[m,e]     : ∀ {i} (i∈ρₛ : i ∈ ρ start) → i IsActiveIn [ m i , end ]

  open SubEpoch η[s,e] public

  η[s,m] : ∀ i → SubEpoch [ start , m i ]
  η[s,m] i = ηₛₑ-inRangeₛ η[s,e] (start≤midᵢ i , midᵢ≤end i)
  
  η[m,e] : ∀ i → SubEpoch [ m i   , end ]
  η[m,e] i = ηₛₑ-inRangeₑ η[s,e] (start≤midᵢ i , midᵢ≤end i)

--------------------------------------------------------------------------------
-- Multi-pseudocycles
--------------------------------------------------------------------------------
-- A time period that contains k pseudocycle.

data MultiPseudocycle : ℕ → TimePeriod → Set₁ where
  none : ∀ {t} → MultiPseudocycle 0 [ t , t ]
  next : ∀ {s} m {e k} →
         Pseudocycle [ s , m ] →
         MultiPseudocycle k [ m , e ] →
         MultiPseudocycle (suc k) [ s , e ]

ηₛ≡ηₑ-mpp : ∀ {s e k} → MultiPseudocycle k [ s , e ] → η s ≡ η e
ηₛ≡ηₑ-mpp none            = refl
ηₛ≡ηₑ-mpp (next m pp mpp) = trans (Pseudocycle.ηₛ≡ηₑ pp) (ηₛ≡ηₑ-mpp mpp)

s≤e-mpp : ∀ {s e k} → MultiPseudocycle k [ s , e ] → s ≤ e
s≤e-mpp none            = ≤-refl
s≤e-mpp (next m pp mpp) = ≤-trans (Pseudocycle.start≤end pp) (s≤e-mpp mpp)
