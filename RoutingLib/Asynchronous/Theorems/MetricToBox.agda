open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ≤) renaming (_≤_ to _≤𝔽_; _<_ to _<𝔽_)
open import Data.Fin.Properties using (fromℕ≤-toℕ; prop-toℕ-≤′)
open import Data.Nat using (ℕ; _≤_; _<_; z≤n; s≤s; zero; suc; _+_; _∸_) renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (≤-decTotalOrder; _<?_; ≤-refl; <-transʳ; ≤-trans; n≤1+n; n∸m≤n; <⇒≤; ≮⇒≥; m≤m+n) renaming ()
open import Data.List using (List; []; _∷_; length; concat; tabulate)
open import Data.List.All using (All)
open import Data.List.All.Properties using (All-universal)
open import Data.List.Any using (here; there; index)
open import Data.List.Any.Properties using (lift-resp)
open import Data.List.Any.Membership.Propositional using () renaming (_∈_ to _∈ℕ_)
open import Data.List.Any.Membership.Propositional.Properties using ()
open import Data.Vec using (Vec; _∷_; fromList)
open import Data.Product using (∃; ∃₂; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary using (Setoid; Decidable; IsDecEquivalence; DecSetoid)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; cong; sym; trans; module ≡-Reasoning)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction; ¬?)
open import Function using (_∘_)

open import RoutingLib.Data.Table using (Table; max; zipWith)
open import RoutingLib.Data.Table.Properties using (t≤max[t])
open import RoutingLib.Data.Table.Membership.Propositional.Properties using (max[t]∈t)
open import RoutingLib.Data.Nat.Properties
  using (ℕₛ; n≤0⇒n≡0; m≤n⇒m∸n≡0; m∸[m∸n]≡n; ∸-monoʳ-≤; ∸-monoˡ-<; ∸-cancelʳ-<; module ≤-Reasoning; ℕᵈˢ)
open import RoutingLib.Data.Fin.Properties
  using (fromℕ≤-cong; fromℕ≤-mono-≤; fromℕ≤-mono⁻¹-<)
open import RoutingLib.Data.List using (lookup; dfilter)
open import RoutingLib.Data.List.All using (_∷_)
open import RoutingLib.Data.List.All.Properties using (deduplicate⁺; All-dfilter⁺₁)
open import RoutingLib.Data.List.Properties using ()
open import RoutingLib.Data.List.Any.Properties using (lookup-index)
open import RoutingLib.Data.List.Membership.DecPropositional _≟ℕ_ using (deduplicate)
open import RoutingLib.Data.List.Membership.DecPropositional.Properties
  using (∈-deduplicate⁻; ∈-deduplicate⁺; ∈-concat⁺; ∈-dfilter⁺; ∈-resp-≡)
open import RoutingLib.Data.List.Sorting.Mergesort ≤-decTotalOrder
open import RoutingLib.Data.List.Sorting ≤-decTotalOrder using (Sorted)
open import RoutingLib.Data.List.Sorting.Properties ≤-decTotalOrder
  using (↗-All; lookup-mono-≤)
open import RoutingLib.Data.List.Sorting.Nat using (index-mono⁻¹-<)
open import RoutingLib.Data.List.Uniqueness.Propositional using (Unique)
open import RoutingLib.Data.List.Uniqueness.Propositional.Properties using (deduplicate!⁺)
open import RoutingLib.Asynchronous using (Parallelisation)
open import RoutingLib.Asynchronous.Theorems.Core using (ACO; UltrametricConditions)
open import RoutingLib.Function.Image using (FiniteImage)
open import RoutingLib.Function.Distance using (IsUltrametric)
open import RoutingLib.Function.Distance.Properties using (strContr⇒strContrOnOrbits)
import RoutingLib.Function.Distance.MaxLift as MaxLift

module RoutingLib.Asynchronous.Theorems.MetricToBox
  {a ℓ n} {S : Fin n → Setoid a ℓ} {P : Parallelisation S}
  (𝓤𝓒 : UltrametricConditions P) where

    open Parallelisation P using (M; f; Pred; _⊂_; _⊆_; _≈_; _≉_; _∈_; isSingleton; ≈-refl; ≈-sym; ≈-isEquivalence; ≈ᵢ-refl; ≈ᵢ-sym; M-setoid)
    open UltrametricConditions 𝓤𝓒
    ≈-isDecEquivalence : IsDecEquivalence _≈_
    ≈-isDecEquivalence = record
      { isEquivalence = ≈-isEquivalence
      ; _≟_           = _≟_
      }

    M-decSetoid : DecSetoid _ _
    M-decSetoid = record
      { Carrier          = M
      ; _≈_              = _≈_
      ; isDecEquivalence = ≈-isDecEquivalence
      }
        
    module _ {i} where

      open IsUltrametric (dᵢ-isUltrametric {i}) renaming
        ( sym  to dᵢ-sym
        ; eq⇒0 to x≈y⇒dᵢ≡0
        ; 0⇒eq to dᵢ≡0⇒x≈y
        ; cong to dᵢ-cong
        ) public


    -- Properties of d
    
    d-isUltrametric : IsUltrametric M-setoid d
    d-isUltrametric = MaxLift.isUltrametric S dᵢ (λ _ → dᵢ-isUltrametric)

    open IsUltrametric d-isUltrametric using () renaming
      ( cong to d-cong
      ; sym to d-sym
      ; 0⇒eq to d≡0⇒x≈y
      ; eq⇒0 to x≈y⇒d≡0
      )

    dᵢ≤d : ∀ x y i → dᵢ (x i) (y i) ≤ d x y
    dᵢ≤d = MaxLift.dᵢ≤d S dᵢ

    open import RoutingLib.Function.Distance M-setoid using (_StrContrOnOrbitsOver_)
    
    f-strContrOnOrbits : f StrContrOnOrbitsOver d
    f-strContrOnOrbits = f-strContrOver-d -- strContr⇒strContrOnOrbits

    -- Fixed points exist

    import RoutingLib.Function.Distance.FixedPoint M-decSetoid as FixedPoints

    x* : M
    x* = FixedPoints.x* d f-strContrOnOrbits element
    
    fx*≈x* : f x* ≈ x*
    fx*≈x* = FixedPoints.x*-fixed d f-strContrOnOrbits element

    --------------------
    -- Non zero radii --
    --------------------

    open FiniteImage (d-finiteImage x*)

    nonZeroRadii : List ℕ
    nonZeroRadii = mergesort (deduplicate (dfilter (¬? ∘ (0 ≟ℕ_)) image))

    nonZeroRadii↗ : Sorted nonZeroRadii
    nonZeroRadii↗ = mergesort↗ _

    nonZeroRadii! : Unique nonZeroRadii
    nonZeroRadii! = mergesort!⁺ (deduplicate!⁺ _≟ℕ_ (dfilter _ image))

    0∉nonZeroRadii : All (0 ≢_) nonZeroRadii
    0∉nonZeroRadii = All-mergesort⁺ (0 ≢_) (deduplicate⁺ ℕᵈˢ (All-dfilter⁺₁ _ image))

    nonZeroRadii-complete : ∀ {m} → x* ≉ m → d x* m ∈ℕ nonZeroRadii
    nonZeroRadii-complete {m} x*≉m = ∈-mergesort⁺ (∈-deduplicate⁺ _≟ℕ_ (∈-dfilter⁺ _ 0≢dx*m (complete m)))
      where
      0≢dx*m : 0 ≢ d x* m
      0≢dx*m 0≡dx*m = x*≉m (d≡0⇒x≈y (sym 0≡dx*m))


    -----------
    -- Radii --
    -----------
    
    radii : List ℕ
    radii = zero ∷ nonZeroRadii

    radii↗ : Sorted radii
    radii↗ = All-universal (λ _ → z≤n) nonZeroRadii ∷ nonZeroRadii↗

    radii! : Unique radii
    radii! = 0∉nonZeroRadii ∷ nonZeroRadii!
    
    radii-complete : ∀ m → d x* m ∈ℕ radii
    radii-complete m with x* ≟ m
    ... | yes x*≈m = ∈-resp-≡ (sym (x≈y⇒d≡0 x*≈m)) refl (here refl)
    ... | no  x*≉m = there (nonZeroRadii-complete x*≉m)


    ---------------------
    -- Finishing times --
    ---------------------
    
    T-1 : ℕ
    T-1 = length nonZeroRadii
    
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
    i-mono-≤ {s} {t} s≤t = fromℕ≤-mono-≤ (T-1∸t<T t) (T-1∸t<T s) (∸-monoʳ-≤ s≤t)

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

    D-finish : ∃ λ T → ∃ λ ξ → ∀ K → isSingleton ξ (D (T + K))
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
      
    f-monotonic-x*≉ : ∀ {t} → t ≉ x* → ∀ {K} → t ∈ D K → f t ∈ D (suc K)
    f-monotonic-x*≉ {t} t≉x* {K} t∈D[K] i with max[t]∈t 0 (λ i → dᵢ (x* i) (t i))
    ... | inj₁ d[x*,t]≡0 = contradiction (≈-sym (d≡0⇒x≈y d[x*,t]≡0)) t≉x*
    ... | inj₂ (j , d[x*,t]≡dⱼ[x*ⱼ,tⱼ]) = test K (f t) (begin
      d x*     (f t)           ≡⟨ d-cong (≈-sym fx*≈x*) ≈-refl ⟩
      d (f x*) (f t)           <⟨ f-strContrOver-d t≉x* ⟩
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


    aco : ACO P _
    aco = record
      { D            = D
      ; D-decreasing = D-decreasing
      ; D-finish     = D-finish
      ; f-monotonic  = f-monotonic
      ; D-subst      = D-subst
      }
