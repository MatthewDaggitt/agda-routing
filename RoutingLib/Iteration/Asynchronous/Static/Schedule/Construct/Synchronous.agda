--------------------------------------------------------------------------------
-- This module constructs the static schedule that corresponds to the fully
-- synchronous computation
--------------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc; _∸_)

module RoutingLib.Iteration.Asynchronous.Static.Schedule.Construct.Synchronous
  {n : ℕ} where

open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; ⊤)
open import Data.Fin.Subset.Properties using (∈⊤)
open import Data.Nat using (z≤n; s≤s; _≤_; _<_; _+_)
open import Data.Nat.Properties

open import RoutingLib.Iteration.Asynchronous.Static.Schedule
import RoutingLib.Iteration.Asynchronous.Static.Schedule.Pseudoperiod
  as Pseudoperiod

--------------------------------------------------------------------------------
-- Definition

αˢʸⁿᶜ : 𝕋 → Subset n
αˢʸⁿᶜ _ = ⊤

βˢʸⁿᶜ : 𝕋 → Fin n → Fin n → 𝕋
βˢʸⁿᶜ zero    _ _ = zero
βˢʸⁿᶜ (suc t) _ _ = t

ψˢʸⁿᶜ : Schedule n
ψˢʸⁿᶜ = record
  { α           = αˢʸⁿᶜ
  ; β           = βˢʸⁿᶜ
  ; β-causality = λ _ _ _ → ≤-refl
  }

--------------------------------------------------------------------------------
-- Properties

open Pseudoperiod ψˢʸⁿᶜ

βˢʸⁿᶜ-expiry : ∀ {t₁ t₂} i j → t₁ < t₂ → t₁ ≤ βˢʸⁿᶜ t₂ i j
βˢʸⁿᶜ-expiry i j (s≤s t₁≤t₂) = t₁≤t₂

ψˢʸⁿᶜ-activeIn : ∀ t i → i IsActiveIn [ t , suc t ]
ψˢʸⁿᶜ-activeIn t i = mkₐᵢ (suc t) ≤-refl ≤-refl ∈⊤

ψˢʸⁿᶜ-activationPeriod : ∀ t → IsActivationPeriod [ t , suc t ]
ψˢʸⁿᶜ-activationPeriod t = mkₐ (n≤1+n t) (ψˢʸⁿᶜ-activeIn t)

ψˢʸⁿᶜ-expiryPeriod : ∀ t → IsExpiryPeriod [ t , t ]
ψˢʸⁿᶜ-expiryPeriod t = mkₑ ≤-refl βˢʸⁿᶜ-expiry

ψˢʸⁿᶜ-pseudoperiodic : ∀ t → IsPseudoperiodic [ t , suc t ]
ψˢʸⁿᶜ-pseudoperiodic t = record
  { m      = t
  ; β[s,m] = ψˢʸⁿᶜ-expiryPeriod t
  ; α[m,e] = ψˢʸⁿᶜ-activationPeriod t
  }

ψˢʸⁿᶜ-multiPseudoperiodic : ∀ t k → IsMultiPseudoperiodic k [ t , t + k ]
ψˢʸⁿᶜ-multiPseudoperiodic t zero    rewrite +-identityʳ t = none
ψˢʸⁿᶜ-multiPseudoperiodic t (suc k) rewrite +-suc t k     =
  next (suc t) (ψˢʸⁿᶜ-pseudoperiodic t) (ψˢʸⁿᶜ-multiPseudoperiodic (suc t) k)
