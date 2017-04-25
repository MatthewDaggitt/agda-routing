open import Level using () renaming (zero to lzero)
open import Data.Nat using (ℕ; zero; suc; s≤s; _<_; _≤_; _∸_; _+_)
open import Data.Nat.Properties using (1+n≰n)
open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; _∈_; ⊤)
open import Data.Fin.Subset.Properties using (∈⊤)
open import Data.Product using (∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import RoutingLib.Data.Nat.Properties using (≤-refl)

module RoutingLib.Asynchronous.Schedule where

  ----------
  -- Time --
  ----------

  𝕋 : Set lzero
  𝕋 = ℕ


  --------------------------
  -- Activation functions --
  --------------------------
  -- An activation function maps times to a subset of active processors
  -- i.e. "α t" is the set of active processors at time t
  𝔸 : ℕ → Set lzero
  𝔸 n = 𝕋 → Subset n

  -- Two activation functions are considered equal if the processors activate in lockstep after some point in time
  _⟦_⟧≈𝔸⟦_⟧_ : ∀ {n} → 𝔸 n → 𝕋 → 𝕋 → 𝔸 n → Set lzero
  α₁ ⟦ t₁ ⟧≈𝔸⟦ t₂ ⟧ α₂ = ∀ t → α₁ (suc t + t₁) ≡ α₂ (suc t + t₂)

  -- An activation function is starvation free if every processor will continue to activate indefinitely
  StarvationFree : ∀ {n} → 𝔸 n → Set lzero
  StarvationFree α = ∀ t i → ∃ λ t' → t < t' × i ∈ α t'


  -------------------------
  -- Data flow functions --
  -------------------------
  -- A data flow function describes how information flows between processors
  -- i.e. "β t i j" is the time at which the information from processor j used at processor i at time t was generated
  𝔹 : ℕ → Set lzero
  𝔹 n = 𝕋 → Fin n → Fin n → 𝕋
  
  -- Two data flow functions are considered equal if after some point in time data originates from the same relative point in time
  -- Note that they need never agree at time zero as data at time zero has no origin.
  _⟦_⟧≈𝔹⟦_⟧_ : ∀ {n} → 𝔹 n → 𝕋 → 𝕋 → 𝔹 n → Set lzero
  β₁ ⟦ t₁ ⟧≈𝔹⟦ t₂ ⟧ β₂ = ∀ t i j → β₁ (suc t + t₁) i j ∸ t₁ ≡ β₂ (suc t + t₂) i j ∸ t₂

  -- A data flow function is causal if data always flows forwards in time.
  Causal : ∀ {n} → 𝔹 n → Set lzero
  Causal β = ∀ t i j → β (suc t) i j < suc t

  -- A data flow function is dynamic if each piece of data is only used a finite number of times (i.e. eventually fresh data will be used).
  Dynamic : ∀ {n} → 𝔹 n → Set lzero
  Dynamic β = ∀ t i j → ∃ λ tᶠ → ∀ {t'} → tᶠ < t' → β t' i j ≢ t
  

  --------------
  -- Schedule --
  --------------
  -- An asynchronous schedule for n processors
  record Schedule (n : ℕ) : Set lzero where
    field
      α              : 𝔸 n
      β              : 𝔹 n
      starvationFree : StarvationFree α
      causal         : Causal β
      dynamic        : Dynamic β

  -- Two schedules are considered equal if their activation and data flow functions are equal
  _⟦_⟧≈⟦_⟧_ : ∀ {n} → Schedule n → 𝕋 → 𝕋 → Schedule n → Set lzero
  𝕤₁ ⟦ t₁ ⟧≈⟦ t₂ ⟧ 𝕤₂ = (α 𝕤₁) ⟦ t₁ ⟧≈𝔸⟦ t₂ ⟧ (α 𝕤₂) × (β 𝕤₁) ⟦ t₁ ⟧≈𝔹⟦ t₂ ⟧ (β 𝕤₂)
    where open Schedule


  -----------------------
  -- Example schedules --
  -----------------------
  -- The "synchronous" schedule

  α-sync : ∀ {n} → 𝔸 n
  α-sync _ = ⊤

  β-sync : ∀ {n} → 𝔹 n
  β-sync zero    _ _ = zero
  β-sync (suc t) _ _ = t

  abstract
    
    α-sync-starvationFree : ∀ {n} → StarvationFree (α-sync {n})
    α-sync-starvationFree t _ = suc t , ≤-refl , ∈⊤

    β-sync-causal : ∀ {n} → Causal (β-sync {n})
    β-sync-causal _ _ _ = ≤-refl

    β-sync-dynamic : ∀ {n} → Dynamic (β-sync {n})
    β-sync-dynamic t _ _ = suc t , λ {(s≤s t<t) refl → 1+n≰n t<t}

  𝕤-sync : ∀ n → Schedule n
  𝕤-sync n = record 
    { α              = α-sync 
    ; β              = β-sync 
    ; starvationFree = α-sync-starvationFree
    ; causal         = β-sync-causal 
    ; dynamic        = β-sync-dynamic 
    }
