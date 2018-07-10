open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Subset using (Subset; _∈_; ⊤; ⁅_⁆)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; subst; cong; sym; trans; module ≡-Reasoning)
open import Data.Product using(∃; _,_)
open import Data.Nat.DivMod using (_mod_)
open import Data.Fin.Subset.Properties using (∈⊤; x∈⁅x⁆)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_)
open import Data.Nat.Properties
open import Function.Equivalence using (Equivalence)
open ≡-Reasoning

open import RoutingLib.Asynchronous.Schedule
open import RoutingLib.Asynchronous.Schedule.Synchronous using (β; causality; finite)
open import RoutingLib.Data.Nat.DivMod

module RoutingLib.Asynchronous.Schedule.RoundRobin where

  -- Round Robin Schedule Functions
  α : {n : ℕ} → 𝕋 → Subset (suc n)
  α {n} t = ⁅ t mod (suc n) ⁆

  mod-properties : ∀ {n} t (i : Fin (suc n)) → i ≡ (t + suc (n + (toℕ i) ∸ (t % (suc n)))) mod (suc n)
  mod-properties {n} t i = begin
    i                                             ≡⟨ sym (toℕ-mod i) ⟩
    toℕ i                               mod suc n ≡⟨ sym (+ʳ-mod (toℕ i) _ (%⇒mod≡0 (t ∸ t % suc n) ([a∸a%n]%n≡0 t n))) ⟩
    (toℕ i + (t ∸ t % suc n))           mod suc n ≡⟨ sym (+ˡ-mod (suc n) _ (n[mod]n≡0 n)) ⟩
    (suc n + (toℕ i + (t ∸ t % suc n))) mod suc n ≡⟨ sym (cong (_mod _) (+-assoc (suc n) _ _)) ⟩
    (suc n + toℕ i + (t ∸ t % suc n))   mod suc n ≡⟨ sym (cong (_mod _) (+-∸-assoc _ (a%n≤a t n)) ) ⟩
    ((suc n + toℕ i) + t ∸ t % suc n)   mod suc n ≡⟨ cong (λ v → (v ∸ t % suc n) mod _) (+-comm _ t) ⟩
    (t + suc (n + toℕ i) ∸ t % suc n)   mod suc n ≡⟨ cong (_mod _) (+-∸-assoc t (≤-trans (a%[1+n]≤n t n) (≤-trans (m≤m+n n _) (n≤m+n 1 _)))  ) ⟩
    (t + (suc (n + toℕ i) ∸ t % suc n)) mod suc n ≡⟨ cong (λ v → (t + v) mod _) (+-∸-assoc 1 (≤-trans (a%[1+n]≤n t n) (m≤m+n n _))) ⟩
    (t + suc (n + toℕ i ∸ t % suc n))   mod suc n ∎

  nonstarvation : ∀ {n} t (i : Fin (suc n)) → ∃ λ k → i ∈ α (t + suc k)
  nonstarvation {n} t i = n + (toℕ i) ∸ (t % (suc n)) ,
                subst (i ∈_) (cong ⁅_⁆ (mod-properties t i)) (x∈⁅x⁆ i)

  -- Round Robin Schedule
  rr-schedule : (n : ℕ) → Schedule (suc n)
  rr-schedule n = record
    { α             = α
    ; β             = β
    ; causality     = causality
    ; nonstarvation = nonstarvation
    ; finite        = finite
    }
