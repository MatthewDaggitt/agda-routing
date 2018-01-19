open import Data.Product using (_×_; ∃; proj₁; proj₂; _,_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s; _≟_; _≤?_; _∸_)
open import Data.Nat.Properties using (≤-antisym; pred-mono; ≤+≢⇒<; ≰⇒≥; +-suc; +-identityʳ; m+n∸m≡n; m≤m+n)
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
  open import RoutingLib.Asynchronous.Theorems.Core 𝕡 using (ACO)
  open import RoutingLib.Data.Table.IndexedTypes S

  iter : M → ℕ → M
  iter x₀ zero = x₀
  iter x₀ (suc K) = f (iter x₀ K)

  module proof {p}
               (x₀ : M)
               (D₀ : Pred p)
               (x₀∈D₀ : x₀ ∈ D₀)
               (D₀-subst : ∀ {x y} → x ≈ y → x ∈ D₀ → y ∈ D₀)
               (_≼_ : ∀ {i} → Rel (Setoid.Carrier (S i)) p)
               (≼-refl : ∀ {i} → Reflexive (_≼_ {i}))
               (≼-reflexive : ∀ {i} → _≈ᵢ_ {i} ⇒ _≼_ {i})
               (≼-antisym : ∀ {i} → Antisymmetric (_≈ᵢ_ {i}) (_≼_ {i}))
               (≼-trans : ∀ {i} → Transitive (_≼_ {i}))
               (closed : ∀ x → x ∈ D₀ → f x ∈ D₀)
               (f-monotone : ∀ {x y} → x ∈ D₀ × y ∈ D₀ → (∀ i → x i ≼ y i) → ∀ i → f x i ≼ f y i)
               (iter-dec : ∀ K i → iter x₀ (suc K) i ≼ iter x₀ K i)
               (iter-converge : ∃ λ T → ∀ t → iter x₀ T ≈ iter x₀ (T + t))
    where

    

    _⊴_ : Rel M p
    s ⊴ t = ∀ i → s i ≼ t i

    ⊴-refl : Reflexive _⊴_
    ⊴-refl i = ≼-refl

    ⊴-reflexive : _≈_ ⇒ _⊴_
    ⊴-reflexive x≈y i = ≼-reflexive (x≈y i)

    ⊴-antisym : Antisymmetric _≈_ _⊴_
    ⊴-antisym s⊴t t⊴s i = ≼-antisym (s⊴t i) (t⊴s i)

    ⊴-trans : Transitive _⊴_
    ⊴-trans s⊴t t⊴u i = ≼-trans (s⊴t i) (t⊴u i)


    -- Convergence time
    T : ℕ
    T = proj₁ iter-converge

    -- Convergence state
    ξ : M
    ξ = iter x₀ T

    -- Sequence of sets
    D : ℕ → Pred p
    D K i = (λ x → (ξ i ≼ x) × (x ≼ iter x₀ K i)) ∩ D₀ i 

    D-subst : ∀ K {x y} → x ≈ y → x ∈ D K → y ∈ D K
    D-subst K x≈y x∈DK i with proj₁ (x∈DK i)
    ... | ξ≼x , x≼iterK =  (≼-trans ξ≼x (≼-reflexive (x≈y i))             ,
                                ≼-trans (≼-reflexive (≈ᵢ-sym (x≈y i))) x≼iterK) ,
                                D₀-subst x≈y (λ j → proj₂ (x∈DK j)) i

    D-decreasing : ∀ K → D (suc K) ⊆ D K
    D-decreasing K x∈DK i with x∈DK i
    ... | ((ξ≼x , x≼iterK), x∈D₀) = (ξ≼x , ≼-trans x≼iterK (iter-dec K i)) , x∈D₀

    closed-trans : ∀ K → iter x₀ K ∈ D₀
    closed-trans zero    i = x₀∈D₀ i
    closed-trans (suc K) i = closed (iter x₀ K) (closed-trans K) i
    
    iter-decreasing : ∀ {k t} → k ≤ t → iter x₀ t ⊴ iter x₀ k
    iter-decreasing {.0} {zero} z≤n = ⊴-refl
    iter-decreasing {k} {suc t} k≤t with k ≟ suc t
    ... | yes refl = ⊴-refl
    ... | no  k≢st = ⊴-trans (iter-dec t) (iter-decreasing {k} {t} (pred-mono (≤+≢⇒< k≤t k≢st)))

    x₀∈D0 : x₀ ∈ D 0
    x₀∈D0 i = (iter-decreasing {0} {T} z≤n i , ≼-refl) , x₀∈D₀ i
    
    T≤K⇒ξ≈iterK : ∀ {K} → T ≤ K → ξ ≈ iter x₀ K
    T≤K⇒ξ≈iterK {K} T≤K = ≈-trans (proj₂ iter-converge (K ∸ T)) (≈-cong (iter x₀) (m+n∸m≡n T≤K))

    ξ≈fξ : ξ ≈ f ξ
    ξ≈fξ i = ≈ᵢ-trans (proj₂ iter-converge 1 i)
             (≈-cong (iter x₀) (trans (+-suc T 0) (cong suc (+-identityʳ T))) i)

    ξ∈DK : ∀ K → ξ ∈ D K
    ξ∈DK K i with K ≤? T
    ... | yes K≤T = (≼-refl , iter-decreasing K≤T i) , closed-trans T i
    ... | no  K≰T = (≼-refl , ≼-reflexive (T≤K⇒ξ≈iterK (≰⇒≥ K≰T) i)) , closed-trans T i

    D-finish : ∃ λ ξ → ∀ K → Singleton-t ξ (D (T + K))
    D-finish = ξ , λ K → ξ∈DK (T + K) ,
               λ t t∈D[T+K] i → ≼-antisym (proj₁ (proj₁ (t∈D[T+K] i)))
               (≼-trans (proj₂ (proj₁ (t∈D[T+K] i))) (iter-decreasing (m≤m+n T K) i)) 

    f-monotonic  : ∀ K {t} → t ∈ D K → f t ∈ D (suc K)
    f-monotonic K {t} t∈DK i = (≼-trans (≼-reflexive (ξ≈fξ i))
              (f-monotone (closed-trans T , t∈D₀) ξ⊴t i) ,
              f-monotone (t∈D₀ , closed-trans K) t⊴iterK i) ,
              closed t t∈D₀ i
              where
              t∈D₀ : t ∈ D₀
              t∈D₀ j = proj₂ (t∈DK j)

              ξ⊴t : ξ ⊴ t
              ξ⊴t j = proj₁ (proj₁ (t∈DK j))

              t⊴iterK : t ⊴ iter x₀ K
              t⊴iterK j = proj₂ (proj₁ (t∈DK j))
 
    aco : ACO p
    aco = record {
      T            = T            ;
      D            = D            ;
      D-subst      = D-subst      ;
      D-decreasing = D-decreasing ;
      D-finish     = D-finish     ;
      f-monotonic  = f-monotonic  
      }
    
        

