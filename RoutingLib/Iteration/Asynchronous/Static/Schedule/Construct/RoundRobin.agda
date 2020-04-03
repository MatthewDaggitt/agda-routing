
module RoutingLib.Iteration.Asynchronous.Static.Schedule.Construct.RoundRobin where

open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Subset using (Subset; _∈_; ⊤; ⁅_⁆)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; subst; cong; sym; trans; module ≡-Reasoning)
open import Data.Product using(∃; _,_)
open import Data.Nat.DivMod using (_%_; _mod_; m%n≤m)
open import Data.Nat.Divisibility
open import Data.Fin.Subset.Properties using (∈⊤; x∈⁅x⁆)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_)
open import Data.Nat.Properties
open import Function.Equivalence using (Equivalence)
open ≡-Reasoning

open import RoutingLib.Iteration.Asynchronous.Static.Schedule
open import RoutingLib.Iteration.Asynchronous.Static.Schedule.Construct.Synchronous
  using (βˢʸⁿᶜ; βˢʸⁿᶜ-causality)
open import RoutingLib.Data.Nat.DivMod
open import RoutingLib.Data.Nat.Divisibility

-- Round Robin Schedule Functions
αʳʳ : {n : ℕ} → 𝕋 → Subset (suc n)
αʳʳ {n} t = ⁅ t mod (suc n) ⁆

rr-schedule : (n : ℕ) → Schedule (suc n)
rr-schedule n = record
  { α             = αʳʳ
  ; β             = βˢʸⁿᶜ
  ; β-causality   = βˢʸⁿᶜ-causality
  }

-- Other properties

mod-properties : ∀ {n} t (i : Fin (suc n)) → i ≡ (t + suc (n + (toℕ i) ∸ (t % (suc n)))) mod (suc n)
mod-properties {n} t i = begin
  i                                             ≡⟨ sym (toℕ-mod i) ⟩
  toℕ i                               mod suc n ≡⟨ sym (+ʳ-mod (toℕ i) (m∸m%n∣n t (suc n))) ⟩
  (toℕ i + (t ∸ t % suc n))           mod suc n ≡⟨ sym (+ˡ-mod _ n∣n) ⟩
  (suc n + (toℕ i + (t ∸ t % suc n))) mod suc n ≡⟨ sym (cong (_mod _) (+-assoc (suc n) _ _)) ⟩
  (suc n + toℕ i + (t ∸ t % suc n))   mod suc n ≡⟨ sym (cong (_mod _) (+-∸-assoc _ (m%n≤m t n)) ) ⟩
  ((suc n + toℕ i) + t ∸ t % suc n)   mod suc n ≡⟨ cong (λ v → (v ∸ t % suc n) mod _) (+-comm _ t) ⟩
  (t + suc (n + toℕ i) ∸ t % suc n)   mod suc n ≡⟨ cong (_mod _) (+-∸-assoc t (≤-trans t%[1+n]≤n+i (m≤n+m _ 1))) ⟩
  (t + (suc (n + toℕ i) ∸ t % suc n)) mod suc n ≡⟨ cong (λ v → (t + v) mod _) (+-∸-assoc 1 t%[1+n]≤n+i) ⟩
  (t + suc (n + toℕ i ∸ t % suc n))   mod suc n ∎
  where t%[1+n]≤n+i = ≤-trans (m%[1+n]≤n t n) (m≤m+n n _)

nonstarvation : ∀ {n} t (i : Fin (suc n)) → ∃ λ k → i ∈ αʳʳ (t + suc k)
nonstarvation {n} t i = n + (toℕ i) ∸ (t % (suc n)) ,
              subst (i ∈_) (cong ⁅_⁆ (mod-properties t i)) (x∈⁅x⁆ i)

