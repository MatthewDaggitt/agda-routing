open import Data.Fin using (Fin)
open import Data.Fin.Subset using () renaming (_∈_ to _∈ₛ_)
open import Data.Fin.Dec using (_∈?_)
open import Data.Product using (∃; proj₂; proj₁; _,_)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using (<-wellFounded)
open import Data.Nat using (ℕ; _+_; _≤_; zero; suc; _<_; _≟_; s≤s; z≤n; _∸_)
open import Data.Nat.Properties
  using (≤-trans; +-identityʳ; m≤m+n; <⇒≱; module ≤-Reasoning;
        <⇒≤pred; ≤+≢⇒<; m+n∸m≡n; ≤-antisym; +-suc; ≤-refl; n≤1+n)
open import Relation.Binary.PropositionalEquality using (subst; cong; refl; sym; trans)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using () renaming (_∈_ to _∈ᵤ_)

open import RoutingLib.Asynchronous
open import RoutingLib.Asynchronous.Schedule
open import RoutingLib.Asynchronous.Schedule.Pseudoperiod.Properties using (pseudoperiodic)
open import RoutingLib.Asynchronous.Convergence.Conditions using (ACO)
open import RoutingLib.Relation.Binary.Indexed.Homogeneous
open import RoutingLib.Relation.Unary.Indexed

module RoutingLib.Asynchronous.Convergence.Proofs.UresinDubois1
  {a ℓ n p} {𝕊 : IndexedSetoid (Fin n) a ℓ} (𝓟 : Parallelisation 𝕊) (aco : ACO 𝓟 p) where

  open Parallelisation 𝓟
  open ACO aco

  -- The final box number
  T : 𝕋
  T = proj₁ D-finish

  -- The final state
  ξ : S
  ξ = proj₁ (proj₂ D-finish)


  module _ (𝓟𝓢 : PseudoperiodicSchedule n) where

    open PseudoperiodicSchedule 𝓟𝓢
    
    β-decreasing : ∀ {t} i j → 1 ≤ t → β t i j ≤ t
    β-decreasing i j (s≤s z≤n) = ≤-trans (causality _ i j) (n≤1+n _)

    τ[1+K]-expired : ∀ {t K i j} → τ (suc K) i ≤ t → τ K j ≤ β t i j
    τ[1+K]-expired {t} {K} {i} {j} τ[1+K]≤t = begin
      τ K j                               ≤⟨ τ-expired K (t ∸ φ (suc K)) i j ⟩
      β (φ (suc K) + (t ∸ φ (suc K))) i j ≡⟨ cong (λ x → β x i j) (m+n∸m≡n (≤-trans (τ-after-φ (suc K) i) τ[1+K]≤t)) ⟩
      β t                             i j ∎
      where open ≤-Reasoning

    0<τ[1+K] : ∀ {K i} → 0 < τ (suc K) i
    0<τ[1+K] {K} {i} = begin
      1            ≤⟨ s≤s z≤n ⟩
      suc K        ≤⟨ φ-increasing (suc K) ⟩
      φ (suc K)    ≤⟨ τ-after-φ (suc K) i ⟩
      τ (suc K) i  ∎
      where open ≤-Reasoning

    module _ {x₀ : S} (x₀∈D₀ : x₀ ∈ D 0) where

      async[t]'∈D₀ : ∀ {t} (accₜ : Acc _<_ t) → asyncIter' 𝓢 x₀ accₜ ∈ D 0
      async[t]'∈D₀ {zero}   _          i = x₀∈D₀ i
      async[t]'∈D₀ {suc t}  (acc rec)  i with i ∈? α (suc t)
      ... | yes i∈α = D-decreasing 0 (F-monotonic (λ j → async[t]'∈D₀ (rec (β (suc t) i j) (s≤s (causality t i j))) j)) i
      ... | no  i∉α = async[t]'∈D₀ (rec t (s≤s ≤-refl)) i

      τ-stability' : ∀ {t K i} (accₜ : Acc _<_ t) → τ K i ≤ t →
                     asyncIter' 𝓢 x₀ accₜ i ∈ᵤ D K
      τ-stability' {_}      {zero}   {i} accₜ       _      = async[t]'∈D₀ accₜ i
      τ-stability' {zero}   {suc K}  {i} _          τ≤0    = contradiction τ≤0 (<⇒≱ 0<τ[1+K])
      τ-stability' {suc t}  {suc K}  {i} (acc rec)  τ≤1+t  with i ∈? α (suc t)
      ... | yes _ = F-monotonic (λ j → τ-stability' _ (τ[1+K]-expired τ≤1+t)) i
      ... | no  i∉α with τ (suc K) i ≟ suc t
      ...   | no  τ≢1+t = τ-stability' _ (<⇒≤pred (≤+≢⇒< τ≤1+t τ≢1+t))
      ...   | yes τ≡1+t = contradiction (subst (i ∈ₛ_) (cong α τ≡1+t) (τ-active (suc K) i)) i∉α

      τ-stability : ∀ {t K i} → τ K i ≤ t → asyncIter 𝓢 x₀ t i ∈ᵤ D K
      τ-stability {t} = τ-stability' (<-wellFounded t)


      -- Theorem 1



      D[T]≈⦃ξ⦄ : ∀ {s} → s ∈ D T → s ≈ ξ
      D[T]≈⦃ξ⦄ {s} s∈D[T] rewrite sym (+-identityʳ T) = ≈-sym (proj₂ (proj₂ (proj₂ D-finish) 0) s∈D[T])

      tᶜ : 𝕋
      tᶜ = φ (suc T)

      1≤tᶜ : 1 ≤ tᶜ
      1≤tᶜ = ≤-trans (s≤s z≤n) (φ-increasing (suc T))

      async[tᶜ]∈D[T] : ∀ t → asyncIter 𝓢 x₀ (tᶜ + t) ∈ D T
      async[tᶜ]∈D[T] t j = τ-stability (begin
        τ T j           ≤⟨ τ-expired T 0 j j ⟩
        β (tᶜ + 0) j j  ≡⟨ cong (λ v → β v j j) (+-identityʳ tᶜ) ⟩
        β tᶜ j j        ≤⟨ β-decreasing j j 1≤tᶜ ⟩
        tᶜ              ≤⟨ m≤m+n tᶜ t ⟩
        tᶜ + t          ∎)
        where open ≤-Reasoning

      async-converge : ∀ K → asyncIter 𝓢 x₀ (tᶜ + K) ≈ ξ
      async-converge K = D[T]≈⦃ξ⦄ (async[tᶜ]∈D[T] K)

  ξ-reached : ∀ {X} → X ∈ D 0 → ∀ s → ∃ λ tᶜ → ∀ t → asyncIter s X (tᶜ + t) ≈ ξ
  ξ-reached X∈D₀ s = tᶜ (pseudoperiodic s) X∈D₀ , async-converge (pseudoperiodic s) X∈D₀

  isPartiallyAsynchronouslySafe : IsPartiallyAsynchronouslySafe 𝓟 (D 0)
  isPartiallyAsynchronouslySafe = record
    { m*         = ξ
    ; m*-reached = ξ-reached
    }
