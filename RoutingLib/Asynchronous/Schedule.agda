open import Level using () renaming (zero to lzero)
open import Data.Nat using (ℕ; zero; suc; pred; s≤s; _<_; _≤_; _∸_; _+_)
open import Data.Nat.Properties using (1+n≰n; ≤-refl; module ≤-Reasoning)
open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; _∈_; ⊤)
open import Data.Fin.Subset.Properties using (∈⊤)
open import Data.Product using (∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

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
  NonStarvation : ∀ {n} → 𝔸 n → Set lzero
  NonStarvation α = ∀ t i → ∃ λ k → i ∈ α (t + suc k)


  -------------------------
  -- Data flow functions --
  -------------------------
  -- A data flow function describes how information flows between processors
  -- i.e. "β t i j" is the time at which the information from processor j used
  -- at processor i at time t was generated
  𝔹 : ℕ → Set lzero
  𝔹 n = 𝕋 → Fin n → Fin n → 𝕋
  
  -- Two data flow functions are considered equal if after some point in time data originates from the same relative point in time
  -- Note that they need never agree at time zero as data at time zero has no origin.
  _⟦_⟧≈𝔹⟦_⟧_ : ∀ {n} → 𝔹 n → 𝕋 → 𝕋 → 𝔹 n → Set lzero
  β₁ ⟦ t₁ ⟧≈𝔹⟦ t₂ ⟧ β₂ = ∀ t i j → β₁ (suc t + t₁) i j ∸ t₁ ≡ β₂ (suc t + t₂) i j ∸ t₂

  -- A data flow function is causal if data always flows forwards in time.
  Causality : ∀ {n} → 𝔹 n → Set lzero
  Causality β = ∀ t i j → β (suc t) i j ≤ t

  -- A data flow function is dynamic if each piece of data is only used a finite number of times (i.e. eventually fresh data will be used).
  Dynamic : ∀ {n} → 𝔹 n → Set lzero
  Dynamic β = ∀ t i j → ∃ λ k → ∀ k₁ → β (t + k + k₁) i j ≢ t
  

  --------------
  -- Schedule --
  --------------

  -- An asynchronous schedule for n processors
  record Schedule (n : ℕ) : Set where
    field
      {- α returns a subset of the shared memory elements that are active at time t -}
      α             : (t : 𝕋) → Subset n
      {- β returns the last time element i was accessed before time t -}
      β             : (t : 𝕋)(i j : Fin n) → 𝕋
      {- A1: Elements can only rely on their past values -}
      causality     : ∀ t i j → β (suc t) i j ≤ t
      {- A2: Each element gets updated infinitely often -}
      nonstarvation : ∀ t i → ∃ λ k → i ∈ α (t + suc k)
      {- A3: Each element will eventually not need its value at time t -}
      finite        : ∀ t i j → ∃ λ k → ∀ l → β (k + l) i j ≢ t
      
      
  -- Two schedules are considered equal if their activation and data flow functions are equal
  _⟦_⟧≈⟦_⟧_ : ∀ {n} → Schedule n → 𝕋 → 𝕋 → Schedule n → Set lzero
  𝕤₁ ⟦ t₁ ⟧≈⟦ t₂ ⟧ 𝕤₂ = (α 𝕤₁) ⟦ t₁ ⟧≈𝔸⟦ t₂ ⟧ (α 𝕤₂) × (β 𝕤₁) ⟦ t₁ ⟧≈𝔹⟦ t₂ ⟧ (β 𝕤₂)
    where open Schedule

