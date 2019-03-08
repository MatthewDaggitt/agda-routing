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
open import Function using (const)

open import RoutingLib.Iteration.Asynchronous.Static.Schedule
import RoutingLib.Iteration.Asynchronous.Static.Schedule.Pseudoperiod
  as Pseudoperiod

--------------------------------------------------------------------------------
-- Definition

αˢʸⁿᶜ : 𝕋 → Subset n
αˢʸⁿᶜ = const ⊤

βˢʸⁿᶜ : 𝕋 → Fin n → Fin n → 𝕋
βˢʸⁿᶜ t _ _ = t ∸ 1

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
ψˢʸⁿᶜ-activeIn t i = mkₐ (suc t) ≤-refl ≤-refl ∈⊤

ψˢʸⁿᶜ-expiresIn : ∀ t i → MessagesTo i ExpireIn [ t , t ]
ψˢʸⁿᶜ-expiresIn t i = mkₑ ≤-refl (βˢʸⁿᶜ-expiry i)

ψˢʸⁿᶜ-pseudocycle : ∀ t → Pseudocycle [ t , suc t ]
ψˢʸⁿᶜ-pseudocycle t = record
  { m          = const t
  ; start≤end  = n≤1+n t
  ; start≤midᵢ = const ≤-refl
  ; midᵢ≤end   = const (n≤1+n t)
  ; β[s,m]     = ψˢʸⁿᶜ-expiresIn t
  ; α[m,e]     = ψˢʸⁿᶜ-activeIn t
  }

ψˢʸⁿᶜ-multiPseudocycle : ∀ t k → MultiPseudocycle k [ t , t + k ]
ψˢʸⁿᶜ-multiPseudocycle t zero    rewrite +-identityʳ t = none
ψˢʸⁿᶜ-multiPseudocycle t (suc k) rewrite +-suc t k     =
  next (suc t) (ψˢʸⁿᶜ-pseudocycle t) (ψˢʸⁿᶜ-multiPseudocycle (suc t) k)
