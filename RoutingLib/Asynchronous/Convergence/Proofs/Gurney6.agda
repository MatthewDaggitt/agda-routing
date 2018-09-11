open import Data.Fin
  using (Fin; zero; suc; toℕ; fromℕ≤) renaming (_≤_ to _≤𝔽_; _<_ to _<𝔽_)
open import Data.Fin.Properties
  using (fromℕ≤-toℕ; prop-toℕ-≤′)
open import Data.Fin.Dec using (all?)
open import Data.Nat
  using (ℕ; _≤_; _<_; z≤n; s≤s; zero; suc; _+_; _∸_; _⊔_) renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties
  using (≤-decTotalOrder; <⇒≢; _<?_; ≤-refl; ≤-antisym; <-transʳ; ≤-trans;
        n≤1+n; n∸m≤n; <⇒≤; ≮⇒≥; m≤m+n; ⊔-sel; <⇒≱; m∸[m∸n]≡n; m≤n⇒n⊔m≡n; m≤n⇒m⊔n≡n
        ; m≤n⇒m∸n≡0; ∸-monoʳ-≤)
open import Data.List
  using (List; []; _∷_; length; upTo; applyUpTo; lookup)
open import Data.List.Any
  using (here; there; index)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ℕ_)
open import Data.Product using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary using (Rel; Decidable; IsDecEquivalence; DecSetoid)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; cong; sym; trans; module ≡-Reasoning)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_)

open import RoutingLib.Data.Table.Membership.Propositional.Properties using (max[t]∈t)
open import RoutingLib.Data.Nat.Properties
  using (ℕₛ; n≤0⇒n≡0; ∸-cancelʳ-<; module ≤-Reasoning; ℕᵈˢ)
open import RoutingLib.Data.Fin.Properties
  using (fromℕ≤-cong; fromℕ≤-mono-≤; fromℕ≤-cancel-<)
open import RoutingLib.Data.List.Any.Properties using (lookup-index)
open import RoutingLib.Data.List.Membership.DecPropositional.Properties using (∈-upTo⁺)
open import RoutingLib.Data.List.Sorting _≤_ using (Sorted)
open import RoutingLib.Data.List.Sorting.Properties ≤-decTotalOrder
  using (lookup-mono-≤)
open import RoutingLib.Data.List.Sorting.Nat using (index-mono⁻¹-<; upTo-↗)
open import RoutingLib.Data.List.Uniqueness.Propositional using (Unique)
open import RoutingLib.Data.List.Uniqueness.Propositional.Properties using (upTo!⁺)
open import RoutingLib.Function.Metric using (IsUltrametric)
import RoutingLib.Function.Metric.MaxLift as MaxLift
import RoutingLib.Function.Metric.FixedPoint as FixedPoints
open import RoutingLib.Relation.Unary.Indexed
open import RoutingLib.Relation.Binary.Indexed.Homogeneous using (IndexedSetoid)

open import RoutingLib.Asynchronous using (Parallelisation)
open import RoutingLib.Asynchronous.Convergence.Conditions using (ACO; UltrametricConditions)

module RoutingLib.Asynchronous.Convergence.Proofs.Gurney6
  {a ℓ n} {𝕊 : IndexedSetoid (Fin n) a ℓ} {P : Parallelisation 𝕊}
  (𝓤𝓒 : UltrametricConditions P) where

    open Parallelisation P
    open UltrametricConditions 𝓤𝓒

    ----------------------------------------------
    -- Export and define some useful properties --
    ----------------------------------------------

    _≟_ : Decidable _≈_
    x ≟ y = all? (λ i → x i ≟ᵢ y i)

    𝕊? : DecSetoid _ _
    𝕊? = record
      { Carrier          = S
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

    d-isUltrametric : IsUltrametric setoid d
    d-isUltrametric = MaxLift.isUltrametric 𝕊 dᵢ-isUltrametric

    open IsUltrametric d-isUltrametric using () renaming
      ( cong to d-cong
      ; sym to d-sym
      ; 0⇒eq to d≡0⇒x≈y
      ; eq⇒0 to x≈y⇒d≡0
      ; maxTriangle to d-maxTriIneq
      )

    dᵢ≤d : ∀ x y i → dᵢ (x i) (y i) ≤ d x y
    dᵢ≤d = MaxLift.dᵢ≤d 𝕊 dᵢ


    ------------------------------
    -- Existence of fixed point --
    ------------------------------

    x* : S
    x* = FixedPoints.x* 𝕊? d F-strContrOnOrbits element

    Fx*≈x* : F x* ≈ x*
    Fx*≈x* = FixedPoints.x*-fixed 𝕊? d F-strContrOnOrbits element

    x*-unique : ∀ {x} → F x ≈ x → x ≈ x*
    x*-unique {x} Fx≈x with x ≟ x*
    ... | yes x≈x* = x≈x*
    ... | no  x≉x* = contradiction (d-cong ≈-refl Fx≈x) (<⇒≢ (F-strContrOnFP Fx*≈x* x≉x*))


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
    i-mono⁻¹-< is<it = ∸-cancelʳ-< (fromℕ≤-cancel-< _ _ is<it)

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

      r-lookup : S → ℕ
      r-lookup m = i-lookup (index (radii-complete m))

      r-lookup-res : ∀ m → r[ r-lookup m ] ≡ d x* m
      r-lookup-res m = begin
        r[ r-lookup m ]                                       ≡⟨⟩
        lookup radii i[ i-lookup (index (radii-complete m)) ] ≡⟨ cong (lookup radii) (i-lookup-res (index (radii-complete m))) ⟩
        lookup radii (index (radii-complete m))               ≡⟨ sym (lookup-index (radii-complete m)) ⟩
        d x* m          ∎
        where open ≡-Reasoning

      ∃K:r[K]≡dx*m : ∀ m → ∃ λ k → r[ k ] ≡ d x* m
      ∃K:r[K]≡dx*m m = r-lookup m , r-lookup-res m



    -----------
    -- Boxes --
    -----------
    -- Definitions of the boxes D

    D : ℕ → Pred Sᵢ _
    D t {i} m = dᵢ (x* i) m ≤ r[ t ]

    -- D is decreasing

    D-decreasing : ∀ K → D (suc K) ⊆ D K
    D-decreasing K {m} m∈D₁₊ₖ i = begin
      dᵢ (x* i) (m i)  ≤⟨ m∈D₁₊ₖ i ⟩
      r[ suc K ]       ≤⟨ r-mono-≤ (n≤1+n K) ⟩
      r[ K ]           ∎
      where open ≤-Reasoning

    -- D(T + K) is the singleton set

    m∈D[T+K]⇒x*≈m : ∀ K {m} → m ∈ D (T + K) → x* ≈ m
    m∈D[T+K]⇒x*≈m K {m} m∈D[T+K] i = dᵢ≡0⇒x≈y (n≤0⇒n≡0 (begin
      dᵢ (x* i) (m i)  ≤⟨ m∈D[T+K] i ⟩
      r[ T + K ]       ≡⟨ r[T+K]≡r[T] K ⟩
      r[ T ]           ≡⟨ r[T]≡0 ⟩
      0                ∎))
      where open ≤-Reasoning

    x*∈D[T+K] : ∀ K → x* ∈ D (T + K)
    x*∈D[T+K] K i = begin
      dᵢ (x* i) (x* i)  ≡⟨ x≈y⇒dᵢ≡0 ≈ᵢ-refl ⟩
      0                 ≤⟨ z≤n ⟩
      r[ T + K ]        ∎
      where open ≤-Reasoning

    D-finish : ∃₂ λ T ξ → ∀ K → ξ ∈ D (T + K) × (∀ {x} → x ∈ D (T + K) → ξ ≈ x) --IsSingleton ξ (D (T + K))
    D-finish = T , x* , λ K → (x*∈D[T+K] K , m∈D[T+K]⇒x*≈m K)

    -- F is monotonic

    test : ∀ K x → d x* x < r[ K ] → x ∈ D (suc K)
    test K x d[x*,x]<radiiᵢ[K] j with ∃K:r[K]≡dx*m x
    ... | (S , r[S]≡dx*m) = begin
      dᵢ (x* j) (x j) ≤⟨ dᵢ≤d x* x j ⟩
      d x* x          ≡⟨ sym r[S]≡dx*m ⟩
      r[ S ]          ≤⟨ r-mono-≤ K<S ⟩
      r[ suc K ]      ∎
      where

      open ≤-Reasoning

      K<S : K < S
      K<S = r-mono⁻¹-< (subst (_< r[ K ]) (sym r[S]≡dx*m) d[x*,x]<radiiᵢ[K])

    F-monotonic-x*≈ : ∀ {t} → t ≈ x* → ∀ {K} → t ∈ D K → F t ∈ D (suc K)
    F-monotonic-x*≈ {t} t≈x* {K} t∈D[K] i = begin
      dᵢ (x* i) (F t i)   ≡⟨ dᵢ-cong ≈ᵢ-refl (F-cong t≈x* i) ⟩
      dᵢ (x* i) (F x* i)  ≡⟨ x≈y⇒dᵢ≡0 (≈ᵢ-sym (Fx*≈x* i)) ⟩
      0                   ≤⟨ z≤n ⟩
      r[ suc K ]          ∎
      where open ≤-Reasoning

    lemma1 : ∀ x → x ≉ x* → d x* x ≤ d x (F x)
    lemma1 x x≉x* with ⊔-sel (d x* (F x)) (d (F x) x)
    ... | inj₂ right = begin
      d x* x                 ≤⟨ d-maxTriIneq x* (F x) x ⟩
      d x* (F x) ⊔ d (F x) x ≡⟨ right ⟩
      d (F x) x              ≡⟨ d-sym (F x) x ⟩
      d x (F x)              ∎
      where open ≤-Reasoning
    ... | inj₁ left = contradiction (begin
        d x* x                 ≤⟨ d-maxTriIneq x* (F x) x ⟩
        d x* (F x) ⊔ d (F x) x ≡⟨ left ⟩
        d x* (F x)             ∎)
        (<⇒≱ (F-strContrOnFP Fx*≈x* x≉x*))
      where open ≤-Reasoning

    lemma2 : ∀ x → x ≉ x* → d x (F x) ≤ d x* x
    lemma2 x x≉x* = begin
      d x (F x)           ≤⟨ d-maxTriIneq x x* (F x) ⟩
      d x x* ⊔ d x* (F x) ≡⟨ cong (_⊔ d x* (F x)) (d-sym x x*) ⟩
      d x* x ⊔ d x* (F x) ≡⟨ m≤n⇒n⊔m≡n (<⇒≤ (F-strContrOnFP Fx*≈x* x≉x*)) ⟩
      d x* x              ∎
      where open ≤-Reasoning

    lemma : ∀ x → d x* x ≡ d x (F x)
    lemma x with x ≟ x*
    ... | no  x≉x* = ≤-antisym (lemma1 x x≉x*) (lemma2 x x≉x*)
    ... | yes x≈x* = begin
      d x* x       ≡⟨ d-cong ≈-refl x≈x* ⟩
      d x* x*      ≡⟨ d-cong ≈-refl (≈-sym Fx*≈x*) ⟩
      d x* (F x*)  ≡⟨ sym (d-cong x≈x* (F-cong x≈x*)) ⟩
      d x  (F x)   ∎
      where open ≡-Reasoning

    F-monotonic-x*≉ : ∀ {t} → t ≉ x* → ∀ {K} → t ∈ D K → F t ∈ D (suc K)
    F-monotonic-x*≉ {t} t≉x* {K} t∈D[K] i with max[t]∈t 0 (λ i → dᵢ (x* i) (t i))
    ... | inj₁ d[x*,t]≡0 = contradiction (≈-sym (d≡0⇒x≈y d[x*,t]≡0)) t≉x*
    ... | inj₂ (j , d[x*,t]≡dⱼ[x*ⱼ,tⱼ]) with F t ≟ t
    ...   | yes F[t]≈t = contradiction (x*-unique F[t]≈t) t≉x*
    ...   | no  F[t]≉t = test K (F t) (begin
      d x*     (F t)      ≡⟨ lemma (F t) ⟩
      d (F t)  (F (F t))  <⟨ F-strContrOnOrbits F[t]≉t ⟩
      d t      (F t)      ≡⟨ sym (lemma t) ⟩
      d x*     t          ≡⟨ d[x*,t]≡dⱼ[x*ⱼ,tⱼ] ⟩
      dᵢ (x* j) (t j)     ≤⟨ t∈D[K] j ⟩
      r[ K ]              ∎) i
      where open ≤-Reasoning

    F-monotonic  : ∀ {K t} → t ∈ D K → F t ∈ D (suc K)
    F-monotonic {K} {t} with t ≟ x*
    ... | yes t≈x* = F-monotonic-x*≈ t≈x* {K}
    ... | no  t≉x* = F-monotonic-x*≉ t≉x* {K}

    x∈D[0] : ∀ x → x ∈ D 0
    x∈D[0] x i with ∃K:r[K]≡dx*m x
    ... | (t , r[t]≡dx*m) = begin
      dᵢ (x* i) (x i) ≤⟨ dᵢ≤d x* x i ⟩
      d   x*     x    ≡⟨ sym r[t]≡dx*m ⟩
      r[ t ]          ≤⟨ r-mono-≤ z≤n ⟩
      r[ 0 ]          ∎
      where open ≤-Reasoning

    aco : ACO P _
    aco = record
      { D            = D
      ; D-decreasing = D-decreasing
      ; D-finish     = D-finish
      ; F-monotonic  = F-monotonic
      }
