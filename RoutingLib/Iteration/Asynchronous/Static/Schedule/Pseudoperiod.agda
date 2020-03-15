--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module defines what it means for a period of time to be a pseudoperiod
-- with respect to some schedule. As is shown by the proofs in the module
-- `RoutingLib.Iteration.Asynchronous.Static.Convergence.ACOImpliesConvergent`
-- during a pseudoperiod the asynchronous iteration will make at least as much
-- progress towards the fixed point as a single synchronous iteration.
--------------------------------------------------------------------------------

open import RoutingLib.Iteration.Asynchronous.Static.Schedule

module RoutingLib.Iteration.Asynchronous.Static.Schedule.Pseudoperiod
  {n} (ψ : Schedule n) where

open import Level using () renaming (zero to lzero)
open import Data.Fin using (Fin)
open import Data.Fin.Subset using (_∈_; _∉_)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _<_; _≤_; _∸_; _≟_; _⊔_; _+_)
open import Data.Nat.Properties
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Data.List using (foldr; tabulate; applyUpTo)
open import Data.Product using (∃; _×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; subst)
open import Relation.Nullary using (¬_; yes; no)

open Schedule ψ

--------------------------------------------------------------------------------
-- Activation periods --
--------------------------------------------------------------------------------
-- In activation period every participating node is activated at least once.
--
-- Activation periods are typically named α[s,e]

record _IsActiveIn_ (i : Fin n) (period : TimePeriod) : Set where
  constructor mkₐ
  open TimePeriod period
  field
    tₐ       : 𝕋
    s<tₐ     : start < tₐ
    tₐ≤e     : tₐ ≤ end
    i∈α[tₐ]  : i ∈ α tₐ

  start≤end : start ≤ end
  start≤end = ≤-trans (<⇒≤ s<tₐ) tₐ≤e

--------------------------------------------------------------------------------
-- Expiry periods --
--------------------------------------------------------------------------------
-- After the end of an expiry period, there are no messages left in flight that
-- originate from before the start of the expiry period.
--
-- Expiry periods are typically named β[s,e]

record MessagesTo_ExpireIn_ (i : Fin n) (period : TimePeriod) : Set where
  constructor mkₑ
  open TimePeriod period
  field
    start≤end : start ≤ end
    expiryᵢ   : ∀ {t} → end < t → ∀ j → start ≤ β t i j

β[0,0] : ∀ i → MessagesTo i ExpireIn [ 0 , 0 ]
β[0,0] i = mkₑ z≤n (λ 0<t j → z≤n)

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
    start≤end  : start ≤ end
    start≤midᵢ : ∀ i → start ≤ m i
    midᵢ≤end   : ∀ i → m i ≤ end
    
    β[s,m]     : ∀ i → MessagesTo i ExpireIn [ start , m i  ]
    α[m,e]     : ∀ i → i IsActiveIn [ m i , end ]

--------------------------------------------------------------------------------
-- Multi-pseudocycles
--------------------------------------------------------------------------------
-- A time period that contains k distinct pseudocycles

data MultiPseudocycle : ℕ → TimePeriod → Set₁ where
  none : ∀ {t} → MultiPseudocycle 0 [ t , t ]
  next : ∀ {s} m {e k} →
         Pseudocycle [ s , m ] →
         MultiPseudocycle k [ m , e ] →
         MultiPseudocycle (suc k) [ s , e ]


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
