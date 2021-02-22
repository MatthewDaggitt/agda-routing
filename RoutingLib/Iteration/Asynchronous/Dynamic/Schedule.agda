--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module contains the definition of dynamic schedules.
--------------------------------------------------------------------------------

module RoutingLib.Iteration.Asynchronous.Dynamic.Schedule where

open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Nat using (ℕ; zero; suc; pred; z≤n; s≤s; _≟_; _<_; _≤_; _∸_; _+_)
open import Data.Nat.Properties using (n≤1+n; ≤-trans; ≤-antisym)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Subset using (Subset; _∈_; _∉_; _⊆_; ⊤)
open import Data.Product using (∃; _×_; _,_)
open import Function using (const)
open import Relation.Binary using (_Preserves_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; trans; subst)
open import Relation.Unary using (Pred) renaming (_∈_ to _∈ᵤ_)

import RoutingLib.Iteration.Asynchronous.Static.Schedule as StaticSchedules

--------------------------------------------------------------------------------
-- Re-export contents of static schedules publicly

open StaticSchedules public renaming (Schedule to StaticSchedule)

--------------------------------------------------------------------------------
-- Epoch schedules -- schedule dictating the changing nature of the computation

Epoch : Set
Epoch = ℕ

record EpochSchedule (n : ℕ) : Set where
  field
    -- "η t" is the current epoch at time t
    η : (t : 𝕋) → Epoch
    -- "π e" is the set of participating nodes in epoch e
    π : Epoch → Subset n

    -- Epochs increase monotonically
    η-mono         : η Preserves _≤_ ⟶ _≤_

  -- "ρ t" is the set of participants at time t
  ρ : 𝕋 → Subset n
  ρ t = π (η t)

  ∈ρ-subst : ∀ {s e} → η s ≡ η e → ∀ {i} → i ∈ ρ s → i ∈ ρ e
  ∈ρ-subst ηₛ≡ηₑ {i} i∈ρₛ = subst (λ v → i ∈ π v) ηₛ≡ηₑ i∈ρₛ

  -- If two points are in an epoch then any point in between them is also in that epoch
  η-inRangeₛ : ∀ {s e} → η s ≡ η e → ∀ {t} → t ∈ₜ [ s , e ] → η s ≡ η t
  η-inRangeₛ ηₛ≡ηₑ (s≤t , t≤e) = ≤-antisym (η-mono s≤t) (subst (η _ ≤_) (sym ηₛ≡ηₑ) (η-mono t≤e))

  η-inRangeₑ : ∀ {s e} → η s ≡ η e → ∀ {t} → t ∈ₜ [ s , e ] → η t ≡ η e
  η-inRangeₑ ηₛ≡ηₑ t∈[s,e] = trans (sym (η-inRangeₛ ηₛ≡ηₑ t∈[s,e])) ηₛ≡ηₑ

  η-inRange : ∀ {s e} → η s ≡ η e → ∀ {t} → t ∈ₜ [ s , e ] → η s ≡ η t × η t ≡ η e
  η-inRange ηₛ≡ηₑ t∈[s,e] = η-inRangeₛ ηₛ≡ηₑ t∈[s,e] , η-inRangeₑ ηₛ≡ηₑ t∈[s,e]

--------------------------------------------------------------------------------
-- A dynamic schedule is a static schedule combined with an epoch schedule

record Schedule (n : ℕ) : Set where
  field
    staticSchedule : StaticSchedule n
    epochSchedule  : EpochSchedule n

  open StaticSchedule staticSchedule public
  open EpochSchedule epochSchedule public

--------------------------------------------------------------------------------
-- Sometimes it is necessary to restrict the allowable sets of participants
-- in the schedule.

_satisfies_ : ∀ {n} → Schedule n → ∀ {p} → Pred (Epoch × Subset n) p → Set p
S satisfies P = ∀ (t : 𝕋) → (η t , ρ t) ∈ᵤ P
  where open Schedule S
