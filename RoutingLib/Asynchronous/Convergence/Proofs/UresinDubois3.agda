open import Data.Product using (_×_; ∃; proj₁; proj₂; _,_; ∃₂)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s; _≟_; _≤?_; _∸_)
open import Data.Nat.Properties using (≤-antisym; pred-mono; ≤+≢⇒<; ≰⇒≥; +-suc; +-comm; +-identityʳ; m+n∸m≡n; m≤m+n; ≤-refl; ≤-step)
open import Relation.Binary using (Setoid; Rel; Reflexive; Antisymmetric; Transitive; _⇒_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (_∩_; U) renaming (_∈_ to _∈ᵤ_)

open import RoutingLib.Data.Table using (Table)

open import RoutingLib.Asynchronous using (Parallelisation)
open import RoutingLib.Asynchronous.Convergence.Conditions

module RoutingLib.Asynchronous.Convergence.Proofs.UresinDubois3
  {a ℓ n p}
  {𝕊ᵢ : Table (Setoid a ℓ) n}
  (𝓟 : Parallelisation 𝕊ᵢ)
  (syncConditions : SynchronousConditions 𝓟 p)
  where

  open import RoutingLib.Data.Table.IndexedTypes 𝕊ᵢ
  open Parallelisation 𝓟 using (F; syncIter)
  open SynchronousConditions syncConditions
  open StartingConditions start
  open M-poset poset hiding (trans)

  -- Synchronous iterations
  σ : ℕ → S
  σ = syncIter x₀

  σ-mono : ∀ {k t} → k ≤ t → σ t ≼ σ k
  σ-mono {_} {zero}  z≤n = ≼-refl
  σ-mono {k} {suc t} k≤t with k ≟ suc t
  ... | yes refl = ≼-refl
  ... | no  k≢st = ≼-trans (iter-decreasing t) (σ-mono {k} {t} (pred-mono (≤+≢⇒< k≤t k≢st)))
  
  σ[K]∈D₀ : ∀ K → σ K ∈ D₀
  σ[K]∈D₀ zero    i = x₀∈D₀ i
  σ[K]∈D₀ (suc K) i = D₀-closed (σ K) (σ[K]∈D₀ K) i
  
  -- Convergence time
  T : ℕ
  T = proj₁ iter-converge
  
  -- Convergence state
  ξ : S
  ξ = σ T
  
  T≤K⇒ξ≈σ[K] : ∀ {K} → T ≤ K → ξ ≈ σ K
  T≤K⇒ξ≈σ[K] {K} T≤K = begin
    ξ               ≈⟨ proj₂ iter-converge (K ∸ T) ⟩
    σ (T + (K ∸ T)) ≡⟨ cong σ (m+n∸m≡n T≤K) ⟩
    σ K             ∎
    where open EqReasoning 𝕊

  ξ≈F[ξ] : ξ ≈ F ξ
  ξ≈F[ξ] = begin
    ξ         ≈⟨ proj₂ iter-converge 1 ⟩
    σ (T + 1) ≡⟨ cong σ (+-comm T 1) ⟩
    σ (1 + T) ≡⟨⟩
    F ξ ∎
    where open EqReasoning 𝕊


  -- Sequence of sets
  D : ℕ → Pred p
  D K i = (λ x → (ξ i ≼ᵢ x) × (x ≼ᵢ σ K i)) ∩ D₀ i 

  x₀∈D[0] : x₀ ∈ D 0
  x₀∈D[0] i = (σ-mono {0} {T} z≤n i , ≼ᵢ-refl) , x₀∈D₀ i
  
  D-decreasing : ∀ K → D (suc K) ⊆ D K
  D-decreasing K x∈DK i with x∈DK i
  ... | ((ξ≼x , x≼iterK), x∈D₀) = (ξ≼x , ≼ᵢ-trans x≼iterK (iter-decreasing K i)) , x∈D₀

    
  ξ∈D[K] : ∀ K → ξ ∈ D K
  ξ∈D[K] K i with K ≤? T
  ... | yes K≤T = (≼ᵢ-refl , σ-mono K≤T i) , σ[K]∈D₀ T i
  ... | no  K≰T = (≼ᵢ-refl , ≼ᵢ-reflexive (T≤K⇒ξ≈σ[K] (≰⇒≥ K≰T) i)) , σ[K]∈D₀ T i

  D-finish : ∃₂ λ T ξ → ∀ K → IsSingleton ξ (D (T + K))
  D-finish = T , ξ , λ K → ξ∈D[K] (T + K) ,
             λ t t∈D[T+K] i → ≼ᵢ-antisym (proj₁ (proj₁ (t∈D[T+K] i)))
             (≼ᵢ-trans (proj₂ (proj₁ (t∈D[T+K] i))) (σ-mono (m≤m+n T K) i)) 

  F-monotonic  : ∀ K {t} → t ∈ D K → F t ∈ D (suc K)
  F-monotonic K {t} t∈DK i = (≼ᵢ-trans (≼ᵢ-reflexive (ξ≈F[ξ] i)) (F-monotone (σ[K]∈D₀ T) t∈D₀ ξ≼t i) ,
    F-monotone t∈D₀ (σ[K]∈D₀ K) t≼iterK i) ,
    D₀-closed t t∈D₀ i
    where
    t∈D₀ : t ∈ D₀
    t∈D₀ j = proj₂ (t∈DK j)

    ξ≼t : ξ ≼ t
    ξ≼t j = proj₁ (proj₁ (t∈DK j))

    t≼iterK : t ≼ σ K
    t≼iterK j = proj₂ (proj₁ (t∈DK j))

  aco : ACO 𝓟 p
  aco = record
    { D            = D
    ; D-decreasing = D-decreasing
    ; D-finish     = D-finish
    ; F-monotonic  = F-monotonic  
    }



