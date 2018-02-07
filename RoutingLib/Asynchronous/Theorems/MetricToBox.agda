open import Data.Fin
  using (Fin; zero; suc; toℕ; fromℕ≤) renaming (_≤_ to _≤𝔽_; _<_ to _<𝔽_)
open import Data.Fin.Properties
  using (fromℕ≤-toℕ; prop-toℕ-≤′)
open import Data.Nat
  using (ℕ; _≤_; _<_; z≤n; s≤s; zero; suc; _+_; _∸_; _⊔_) renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties
  using (≤-decTotalOrder; <⇒≢; _<?_; ≤-refl; ≤-antisym; <-transʳ; ≤-trans;
        n≤1+n; n∸m≤n; <⇒≤; ≮⇒≥; m≤m+n; ⊔-sel; <⇒≱)
open import Data.List
  using (List; []; _∷_; length; upTo; applyUpTo)
open import Data.List.Any
  using (here; there; index)
open import Data.List.Any.Membership.Propositional using () renaming (_∈_ to _∈ℕ_)
open import Data.Product using (∃; ∃₂; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary using (Setoid; Decidable; IsDecEquivalence; DecSetoid)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; cong; sym; trans; module ≡-Reasoning)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_)

open import RoutingLib.Data.Table.Membership.Propositional.Properties using (max[t]∈t)
open import RoutingLib.Data.Nat.Properties
  using (ℕₛ; n≤0⇒n≡0; m≤n⇒m∸n≡0; m∸[m∸n]≡n; ∸-monoʳ-≤; ∸-cancelʳ-<; n≤m⇒m⊔n≡m; module ≤-Reasoning; ℕᵈˢ)
open import RoutingLib.Data.Fin.Properties
  using (fromℕ≤-cong; fromℕ≤-mono-≤; fromℕ≤-mono⁻¹-<)
open import RoutingLib.Data.List using (lookup)
open import RoutingLib.Data.List.Any.Properties using (lookup-index)
open import RoutingLib.Data.List.Membership.DecPropositional.Properties using (∈-upTo⁺)
open import RoutingLib.Data.List.Sorting ≤-decTotalOrder using (Sorted)
open import RoutingLib.Data.List.Sorting.Properties ≤-decTotalOrder
  using (lookup-mono-≤)
open import RoutingLib.Data.List.Sorting.Nat using (index-mono⁻¹-<; upTo-↗)
open import RoutingLib.Data.List.Uniqueness.Propositional using (Unique)
open import RoutingLib.Data.List.Uniqueness.Propositional.Properties using (upTo!⁺)
open import RoutingLib.Function.Metric using (IsUltrametric)
import RoutingLib.Function.Metric.MaxLift as MaxLift
import RoutingLib.Function.Metric.FixedPoint as FixedPoints

open import RoutingLib.Asynchronous using (Parallelisation)
open import RoutingLib.Asynchronous.Theorems.Core using (ACO; TotalACO; UltrametricConditions)

module RoutingLib.Asynchronous.Theorems.MetricToBox
  {a ℓ n} {S : Fin n → Setoid a ℓ} {P : Parallelisation S}
  (𝓤𝓒 : UltrametricConditions P) where

    open Parallelisation P
    open UltrametricConditions 𝓤𝓒

    ----------------------------------------------
    -- Export and define some useful properties --
    ----------------------------------------------
    
    decSetoid : DecSetoid _ _
    decSetoid = record
      { Carrier          = M
      ; _≈_              = _≈_
      ; isDecEquivalence = record
        { isEquivalence = ≈-isEquivalence
        ; _≟_           = _≟_
        }
      }
      
    module _ {i} where

      open IsUltrametric (dᵢ-isUltrametric {i}) renaming
        ( sym  to dᵢ-sym
        ; eq⇒0 to x≈y⇒dᵢ≡0
        ; 0⇒eq to dᵢ≡0⇒x≈y
        ; cong to dᵢ-cong
        ) public
    
    d-isUltrametric : IsUltrametric M-setoid d
    d-isUltrametric = MaxLift.isUltrametric S dᵢ-isUltrametric

    open IsUltrametric d-isUltrametric using () renaming
      ( cong to d-cong
      ; sym to d-sym
      ; 0⇒eq to d≡0⇒x≈y
      ; eq⇒0 to x≈y⇒d≡0
      ; maxTriangle to d-maxTriIneq
      )

    dᵢ≤d : ∀ x y i → dᵢ (x i) (y i) ≤ d x y
    dᵢ≤d = MaxLift.dᵢ≤d S dᵢ


    ------------------------------
    -- Existence of fixed point --
    ------------------------------

    x* : M
    x* = FixedPoints.x* decSetoid d f-strContrOrbits element

    fx*≈x* : f x* ≈ x*
    fx*≈x* = FixedPoints.x*-fixed decSetoid d f-strContrOrbits element
      
    x*-unique : ∀ {x} → f x ≈ x → x ≈ x*
    x*-unique {x} fx≈x with x ≟ x*
    ... | yes x≈x* = x≈x*
    ... | no  x≉x* = contradiction (d-cong ≈-refl fx≈x) (<⇒≢ (f-strContrOnFP fx*≈x* x≉x*))

    
    -----------
    -- Radii --
    -----------

    dₘₐₓ : ℕ
    dₘₐₓ = proj₁ d-bounded

    d≤dₘₐₓ : ∀ x y → d x y ≤ dₘₐₓ
    d≤dₘₐₓ = proj₂ d-bounded
    
    radii : List ℕ
    radii = upTo (suc dₘₐₓ)

    radii↗ : Sorted radii
    radii↗ = upTo-↗ (suc dₘₐₓ)
    
    radii! : Unique radii
    radii! = upTo!⁺ (suc dₘₐₓ)

    radii-complete : ∀ m → d x* m ∈ℕ radii
    radii-complete m = ∈-upTo⁺ (s≤s (d≤dₘₐₓ x* m))


    ---------------------
    -- Finishing times --
    ---------------------
    
    T-1 : ℕ
    T-1 = length {A = ℕ} (applyUpTo suc dₘₐₓ)
    
    T : ℕ
    T = length radii

    T-1≤T+K : ∀ K → T-1 ≤ T + K
    T-1≤T+K K = ≤-trans (n≤1+n T-1) (m≤m+n T K)
    
    T-1∸t<T : ∀ t → T-1 ∸ t < T
    T-1∸t<T t = s≤s (n∸m≤n t T-1)

    T-1∸T≡0 : T-1 ∸ T ≡ 0
    T-1∸T≡0 = m≤n⇒m∸n≡0 (n≤1+n T-1)
    
    T-1∸T+K≡T-1∸T : ∀ K → T-1 ∸ (T + K) ≡ T-1 ∸ T
    T-1∸T+K≡T-1∸T K = trans (m≤n⇒m∸n≡0 (T-1≤T+K K)) (sym T-1∸T≡0)

    
    -----------------------------
    -- Radii indexing function --
    -----------------------------

    i[_] : ℕ → Fin T
    i[ n ] = fromℕ≤ (T-1∸t<T n)

    i[T+K]≡i[T] : ∀ K → i[ T + K ] ≡ i[ T ]
    i[T+K]≡i[T] K = fromℕ≤-cong (T-1∸t<T (T + K)) (T-1∸t<T T) (T-1∸T+K≡T-1∸T K)

    i[T]≡0 : i[ T ] ≡ zero
    i[T]≡0 = fromℕ≤-cong (T-1∸t<T T) (s≤s z≤n) T-1∸T≡0

    i-mono-≤ : ∀ {s t} → s ≤ t → i[ t ] ≤𝔽 i[ s ]
    i-mono-≤ {s} {t} s≤t = fromℕ≤-mono-≤ (T-1∸t<T t) (T-1∸t<T s) (∸-monoʳ-≤ _ s≤t)

    i-mono⁻¹-< : ∀ {s t} → i[ s ] <𝔽 i[ t ] → t < s
    i-mono⁻¹-< is<it = ∸-cancelʳ-< (fromℕ≤-mono⁻¹-< _ _ is<it)

    i-lookup : Fin T → ℕ
    i-lookup t = T-1 ∸ toℕ t

    i-lookup-res : ∀ t → i[ i-lookup t ] ≡ t
    i-lookup-res t = begin
      i[ i-lookup t ]                ≡⟨⟩
      fromℕ≤ (T-1∸t<T (T-1 ∸ toℕ t)) ≡⟨ fromℕ≤-cong _ _ (m∸[m∸n]≡n (prop-toℕ-≤′ t)) ⟩
      fromℕ≤ (s≤s (prop-toℕ-≤′ t))   ≡⟨ fromℕ≤-toℕ t _ ⟩
      t                              ∎
      where open ≡-Reasoning


    ---------------------
    -- Radii functions --
    ---------------------

    abstract
    
      r[_] : ℕ → ℕ
      r[ k ] = lookup radii i[ k ]

      r[T+K]≡r[T] : ∀ K → r[ T + K ] ≡ r[ T ]
      r[T+K]≡r[T] K = cong (lookup radii) (i[T+K]≡i[T] K)
    
      r[T]≡0 : r[ T ] ≡ 0
      r[T]≡0 = cong (lookup radii) i[T]≡0

      r-mono-≤ : ∀ {s t} → s ≤ t → r[ t ] ≤ r[ s ]
      r-mono-≤ s≤t = lookup-mono-≤ radii↗ (i-mono-≤ s≤t)

      r-mono⁻¹-< : ∀ {s t} → r[ t ] < r[ s ] → s < t
      r-mono⁻¹-< r[t]<r[s] = i-mono⁻¹-< (index-mono⁻¹-< radii↗ radii! r[t]<r[s])

      r-lookup : M → ℕ
      r-lookup m = i-lookup (index (radii-complete m))

      r-lookup-res : ∀ m → r[ r-lookup m ] ≡ d x* m
      r-lookup-res m = begin
        r[ r-lookup m ]                                       ≡⟨⟩
        lookup radii i[ i-lookup (index (radii-complete m)) ] ≡⟨ cong (lookup radii) (i-lookup-res (index (radii-complete m))) ⟩
        lookup radii (index (radii-complete m))               ≡⟨ sym (lookup-index (radii-complete m)) ⟩
        d x* m          ∎
        where open ≡-Reasoning
      
      r≡dx*m : ∀ m → ∃ λ k → r[ k ] ≡ d x* m
      r≡dx*m m = r-lookup m , r-lookup-res m



    -----------
    -- Boxes --
    -----------
    -- Definitions of the boxes D

    D : ℕ → Pred _
    D t i m = dᵢ (x* i) m ≤ r[ t ]

    -- D is decreasing
    
    D-decreasing : ∀ K → D (suc K) ⊆ D K
    D-decreasing K {m} m∈D₁₊ₖ i = begin
      dᵢ (x* i) (m i)  ≤⟨ m∈D₁₊ₖ i ⟩
      r[ suc K ]      ≤⟨ r-mono-≤ (n≤1+n K) ⟩
      r[ K ]          ∎
      where open ≤-Reasoning

    -- D is finishing
    
    m∈D[T+K]⇒x*≈m : ∀ K m → m ∈ D (T + K) → x* ≈ m
    m∈D[T+K]⇒x*≈m K m m∈D[T+K] i = dᵢ≡0⇒x≈y (n≤0⇒n≡0 (begin
      dᵢ (x* i) (m i)          ≤⟨ m∈D[T+K] i ⟩
      r[ T + K ]              ≡⟨ r[T+K]≡r[T] K ⟩
      r[ T ]                  ≡⟨ r[T]≡0 ⟩
      0 ∎))
      where open ≤-Reasoning
      
    x*∈D[T+K] : ∀ K → x* ∈ D (T + K)
    x*∈D[T+K] K i = subst (_≤ r[ T + K ]) (sym (x≈y⇒dᵢ≡0 ≈ᵢ-refl)) z≤n

    D-finish : ∃₂ λ T ξ → ∀ K → IsSingleton ξ (D (T + K))
    D-finish = T , x* , λ K → (x*∈D[T+K] K , m∈D[T+K]⇒x*≈m K)

    test : ∀ K (x : M) → d x* x < r[ K ] → x ∈ D (suc K)
    test K x d[x*,x]<radiiᵢ[K] j with r≡dx*m x
    ... | (S , r[S]≡dx*m) = begin
      dᵢ (x* j) (x j) ≤⟨ dᵢ≤d x* x j ⟩
      d x* x          ≡⟨ sym r[S]≡dx*m ⟩
      r[ S ]          ≤⟨ r-mono-≤ K<S ⟩
      r[ suc K ]      ∎
      where

      open ≤-Reasoning
      
      K<S : K < S
      K<S = r-mono⁻¹-< (subst (_< r[ K ]) (sym r[S]≡dx*m) d[x*,x]<radiiᵢ[K])

    f-monotonic-x*≈ : ∀ {t} → t ≈ x* → ∀ {K} → t ∈ D K → f t ∈ D (suc K) 
    f-monotonic-x*≈ {t} t≈x* {K} t∈D[K] i = begin
      dᵢ (x* i) (f t i)   ≡⟨ dᵢ-cong ≈ᵢ-refl (f-cong t≈x* i) ⟩
      dᵢ (x* i) (f x* i)  ≡⟨ x≈y⇒dᵢ≡0 (≈ᵢ-sym (fx*≈x* i)) ⟩
      0                   ≤⟨ z≤n ⟩
      r[ suc K ]          ∎
      where open ≤-Reasoning


    lemma1 : ∀ x → x ≉ x* → d x* x ≤ d x (f x)
    lemma1 x x≉x* with ⊔-sel (d x* (f x)) (d (f x) x)
    ... | inj₁ left = contradiction tv (<⇒≱ (f-strContrOnFP fx*≈x* x≉x*))
      where
      open ≤-Reasoning
      
      tv : d x* x ≤ d x* (f x)
      tv = begin
        d x* x                 ≤⟨ d-maxTriIneq x* (f x) x ⟩
        d x* (f x) ⊔ d (f x) x ≡⟨ left ⟩
        d x* (f x)             ∎
      
    ... | inj₂ right = begin
      d x* x                 ≤⟨ d-maxTriIneq x* (f x) x ⟩
      d x* (f x) ⊔ d (f x) x ≡⟨ right ⟩
      d (f x) x              ≡⟨ d-sym (f x) x ⟩
      d x (f x)              ∎
      where open ≤-Reasoning
      
    lemma2 : ∀ x → x ≉ x* → d x (f x) ≤ d x* x
    lemma2 x x≉x* = begin
      d x (f x)           ≤⟨ d-maxTriIneq x x* (f x) ⟩
      d x x* ⊔ d x* (f x) ≡⟨ cong (_⊔ d x* (f x)) (d-sym x x*) ⟩
      d x* x ⊔ d x* (f x) ≡⟨ n≤m⇒m⊔n≡m (<⇒≤ (f-strContrOnFP fx*≈x* x≉x*)) ⟩
      d x* x              ∎
      where open ≤-Reasoning
      
    lemma : ∀ x → d x* x ≡ d x (f x)
    lemma x with x ≟ x*
    ... | yes x≈x* = d-cong (≈-sym x≈x*) (≈-trans (≈-trans x≈x* (≈-sym fx*≈x*)) (f-cong (≈-sym x≈x*)))
    ... | no  x≉x* = ≤-antisym (lemma1 x x≉x*) (lemma2 x x≉x*)


    f-monotonic-x*≉ : ∀ {t} → t ≉ x* → ∀ {K} → t ∈ D K → f t ∈ D (suc K)
    f-monotonic-x*≉ {t} t≉x* {K} t∈D[K] i with max[t]∈t 0 (λ i → dᵢ (x* i) (t i))
    ... | inj₁ d[x*,t]≡0 = contradiction (≈-sym (d≡0⇒x≈y d[x*,t]≡0)) t≉x*
    ... | inj₂ (j , d[x*,t]≡dⱼ[x*ⱼ,tⱼ]) with f t ≟ t
    ...   | yes ft≈t = contradiction (x*-unique ft≈t) t≉x*
    ...   | no  ft≉t = test K (f t) (begin
      d x*     (f t)           ≡⟨ lemma (f t) ⟩
      d (f t)  (f (f t))       <⟨ f-strContrOrbits ft≉t ⟩
      d t      (f t)           ≡⟨ sym (lemma t) ⟩
      d x*     t               ≡⟨ d[x*,t]≡dⱼ[x*ⱼ,tⱼ] ⟩
      dᵢ (x* j) (t j)          ≤⟨ t∈D[K] j ⟩
      r[ K ]                   ∎) i
      where open ≤-Reasoning


    f-monotonic  : ∀ K {t} → t ∈ D K → f t ∈ D (suc K)
    f-monotonic K {t} with t ≟ x*
    ... | yes t≈x* = f-monotonic-x*≈ t≈x* {K}
    ... | no  t≉x* = f-monotonic-x*≉ t≉x* {K}
      
    D-subst : ∀ K {x y} → x ≈ y → x ∈ D K → y ∈ D K
    D-subst K {x} {y} x≈y x∈D[K] i = begin
      dᵢ (x* i) (y i)  ≡⟨ dᵢ-cong ≈ᵢ-refl (≈ᵢ-sym (x≈y i)) ⟩
      dᵢ (x* i) (x i)  ≤⟨ x∈D[K] i ⟩
      r[ K ]           ∎
      where open ≤-Reasoning

    total : ∀ x → x ∈ D zero
    total x i with r≡dx*m x
    ... | (t , r[t]≡dx*m) = begin
      dᵢ (x* i) (x i) ≤⟨ dᵢ≤d x* x i ⟩
      d   x*     x    ≡⟨ sym r[t]≡dx*m ⟩
      r[ t    ]       ≤⟨ r-mono-≤ z≤n ⟩
      r[ zero ]       ∎
      where open ≤-Reasoning
      
    aco : ACO P _
    aco = record
      { D            = D
      ; D-decreasing = D-decreasing
      ; D-finish     = D-finish
      ; f-monotonic  = f-monotonic
      ; D-subst      = D-subst
      }

    totalACO : TotalACO P _
    totalACO = record
      { aco   = aco
      ; total = total
      }
