open import Data.Product using (_×_; ∃; proj₁; proj₂; _,_; ∃₂)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s; _≟_; _≤?_; _∸_)
open import Data.Nat.Properties using (≤-antisym; pred-mono; ≤+≢⇒<; ≰⇒≥; +-suc; +-identityʳ; m+n∸m≡n; m≤m+n; ≤-refl; ≤-step)
open import Relation.Binary using (Setoid; Rel; Reflexive; Antisymmetric; Transitive; _⇒_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (_∩_; U) renaming (_∈_ to _∈ᵤ_)

open import RoutingLib.Asynchronous using (Parallelisation)
open import RoutingLib.Data.Table using (Table)

module RoutingLib.Asynchronous.Propositions.UresinDubois3 {a ℓ n}
                                                          {S : Table (Setoid a ℓ) n}
                                                          (𝕡 : Parallelisation S)
  where

  open Parallelisation 𝕡 using (f)
  open import RoutingLib.Asynchronous.Theorems.Core 𝕡 using (ACO; Start; SynchronousConditions; iter)
  open import RoutingLib.Data.Table.IndexedTypes S

  module Proof {p} (syncConditions : SynchronousConditions p) where

    open SynchronousConditions syncConditions
    open Start start
    open M-poset poset hiding (trans)
    
    -- Convergence time
    T : ℕ
    T = proj₁ iter-converge

    -- Convergence state
    ξ : M
    ξ = iter x₀ T

    -- Sequence of sets
    D : ℕ → Pred p
    D K i = (λ x → (ξ i ≼ᵢ x) × (x ≼ᵢ iter x₀ K i)) ∩ D₀ i 

    -- Substitutive Property on D
    D-subst : ∀ K {x y} → x ≈ y → x ∈ D K → y ∈ D K
    D-subst K x≈y x∈DK i with proj₁ (x∈DK i)
    ... | ξ≼x , x≼iterK =  (≼ᵢ-trans ξ≼x (≼ᵢ-reflexive (x≈y i))             ,
                                ≼ᵢ-trans (≼ᵢ-reflexive (≈ᵢ-sym (x≈y i))) x≼iterK) ,
                                D₀-subst x≈y (λ j → proj₂ (x∈DK j)) i

    -- Sequence D(K) is decreasing
    D-decreasing : ∀ K → D (suc K) ⊆ D K
    D-decreasing K x∈DK i with x∈DK i
    ... | ((ξ≼x , x≼iterK), x∈D₀) = (ξ≼x , ≼ᵢ-trans x≼iterK (iter-decreasing K i)) , x∈D₀

    -- All synchronous iterations are in D₀
    closed-trans : ∀ K → iter x₀ K ∈ D₀
    closed-trans zero    i = x₀∈D₀ i
    closed-trans (suc K) i = D₀-closed (iter x₀ K) (closed-trans K) i

    -- Synchronous iteration is monotonic
    iter-decreasing-full : ∀ {k t} → k ≤ t → iter x₀ t ≼ iter x₀ k
    iter-decreasing-full {.0} {zero} z≤n = ≼-refl
    iter-decreasing-full {k} {suc t} k≤t with k ≟ suc t
    ... | yes refl = ≼-refl
    ... | no  k≢st = ≼-trans (iter-decreasing t)
      (iter-decreasing-full {k} {t} (pred-mono (≤+≢⇒< k≤t k≢st)))

    x₀∈D0 : x₀ ∈ D 0
    x₀∈D0 i = (iter-decreasing-full {0} {T} z≤n i , ≼ᵢ-refl) , x₀∈D₀ i

    -- All synchronous iterations after the convergence time equal ξ
    T≤K⇒ξ≈iterK : ∀ {K} → T ≤ K → ξ ≈ iter x₀ K
    T≤K⇒ξ≈iterK {K} T≤K = ≈-trans (proj₂ iter-converge (K ∸ T)) (≈-cong (iter x₀) (m+n∸m≡n T≤K))

    -- ξ is a fixed point
    ξ≈fξ : ξ ≈ f ξ
    ξ≈fξ i = ≈ᵢ-trans (proj₂ iter-converge 1 i)
             (≈-cong (iter x₀) (trans (+-suc T 0) (cong suc (+-identityʳ T))) i)

    -- ξ is in all D(K)
    ξ∈DK : ∀ K → ξ ∈ D K
    ξ∈DK K i with K ≤? T
    ... | yes K≤T = (≼ᵢ-refl , iter-decreasing-full K≤T i) , closed-trans T i
    ... | no  K≰T = (≼ᵢ-refl , ≼ᵢ-reflexive (T≤K⇒ξ≈iterK (≰⇒≥ K≰T) i)) , closed-trans T i

    D-finish : ∃₂ λ T ξ → ∀ K → IsSingleton ξ (D (T + K))
    D-finish = T , ξ , λ K → ξ∈DK (T + K) ,
               λ t t∈D[T+K] i → ≼ᵢ-antisym (proj₁ (proj₁ (t∈D[T+K] i)))
               (≼ᵢ-trans (proj₂ (proj₁ (t∈D[T+K] i))) (iter-decreasing-full (m≤m+n T K) i)) 

    f-monotonic  : ∀ K {t} → t ∈ D K → f t ∈ D (suc K)
    f-monotonic K {t} t∈DK i = (≼ᵢ-trans (≼ᵢ-reflexive (ξ≈fξ i))
              (f-monotone (closed-trans T) t∈D₀ ξ≼t i) ,
              f-monotone t∈D₀ (closed-trans K) t≼iterK i) ,
              D₀-closed t t∈D₀ i
              where
              t∈D₀ : t ∈ D₀
              t∈D₀ j = proj₂ (t∈DK j)

              ξ≼t : ξ ≼ t
              ξ≼t j = proj₁ (proj₁ (t∈DK j))

              t≼iterK : t ≼ iter x₀ K
              t≼iterK j = proj₂ (proj₁ (t∈DK j))
 
    aco : ACO p
    aco = record {
      D            = D            ;
      D-subst      = D-subst      ;
      D-decreasing = D-decreasing ;
      D-finish     = D-finish     ;
      f-monotonic  = f-monotonic  
      }
    
        

