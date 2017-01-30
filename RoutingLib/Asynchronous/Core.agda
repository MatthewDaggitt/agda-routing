open import Level using () renaming (zero to lzero)
open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; _∈_)
open import Data.Nat using (ℕ; _<_; suc)
open import Data.Bool using (Bool)
open import Data.Product using (∃; _×_)
open import Relation.Binary.PropositionalEquality using (_≢_)

module RoutingLib.Asynchronous.Core (n : ℕ) where

  -- An asynchronous schedule for n processors
  -- "α t" is the set of active processors at time t
  -- "β i j t" is the time at which the information from j used at i at time t was generated
  record Schedule : Set lzero where
    field
      α : ℕ → Subset n
      β : ℕ → Fin n → Fin n → ℕ


  -- Conditions for a "reasonable" schedule of events
  record AdmissableSchedule : Set lzero where
    field
      schedule : Schedule

    open Schedule schedule public

    field
      infiniteActivation : ∀ t i → ∃ λ t' → t < t' × i ∈ α t'
      causality :          ∀ t i j → β (suc t) i j < suc t
      eventualExpiry :     ∀ t i j → ∃ λ tᶠ → ∀ {t'} → tᶠ < t' → β t' i j ≢ t
      




