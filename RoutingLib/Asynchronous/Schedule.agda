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

  𝕋 : Set
  𝕋 = ℕ

  --------------------------
  -- Activation functions --
  --------------------------
  -- An activation function maps times to a subset of active processors
  -- i.e. "α t" is the set of active processors at time t
  𝔸 : ℕ → Set
  𝔸 n = 𝕋 → Subset n

  -- An activation function is starvation free if every processor will continue
  -- to activate indefinitely
  NonStarvation : ∀ {n} → 𝔸 n → Set
  NonStarvation α = ∀ t i → ∃ λ k → i ∈ α (t + suc k)

  -------------------------
  -- Data flow functions --
  -------------------------
  -- A data flow function describes how information flows between processors
  -- i.e. "β t i j" is the time at which the information from processor j used
  -- at processor i at time t was generated
  𝔹 : ℕ → Set
  𝔹 n = 𝕋 → Fin n → Fin n → 𝕋
  
  -- A data flow function is causal if data always flows forwards in time.
  Causality : ∀ {n} → 𝔹 n → Set
  Causality β = ∀ t i j → β (suc t) i j ≤ t

  -- A data flow function is dynamic if each piece of data is only used a finite
  -- number of times (i.e. eventually fresh data will be used).
  Dynamic : ∀ {n} → 𝔹 n → Set
  Dynamic β = ∀ t i j → ∃ λ k → ∀ k₁ → β (t + k + k₁) i j ≢ t
  
  --------------
  -- Schedule --
  --------------

  -- An asynchronous schedule for n processors
  record Schedule (n : ℕ) : Set where
    field
      -- α returns a subset of the shared memory elements that are active at time t
      α             : (t : 𝕋) → Subset n
      -- β returns the last time element i was accessed before time t
      β             : (t : 𝕋)(i j : Fin n) → 𝕋
      -- A1: Elements can only rely on their past values
      causality     : ∀ t i j → β (suc t) i j ≤ t
      -- A2: Each element gets updated infinitely often
      nonstarvation : ∀ t i → ∃ λ k → i ∈ α (t + suc k)
      -- A3: Each element will eventually not need its value at time t
      finite        : ∀ t i j → ∃ λ k → ∀ l → β (k + l) i j ≢ t


  -----------------------------
  -- Pseudoperiodic schedule --
  -----------------------------

  record IsPseudoperiodic {n : ℕ} (𝓢 : Schedule n) : Set where
    open Schedule 𝓢
    field
      φ : ℕ → 𝕋
      τ : ℕ → Fin n → 𝕋

      -- Properties of φ
      φ-increasing : ∀ K → K ≤ φ K

      -- Properties of τ
      τ-expired        : ∀ K t i j → τ K j ≤ β (φ (suc K) + t) i j
      τ-after-φ        : ∀ K i → φ K ≤ τ K i
      τ-active         : ∀ K i → i ∈ α (τ K i)


  record PseudoperiodicSchedule (n : ℕ) : Set where

    field
      𝓢 : Schedule n
      isPseudoperiodic : IsPseudoperiodic 𝓢

    open Schedule 𝓢 public
    open IsPseudoperiodic isPseudoperiodic public
