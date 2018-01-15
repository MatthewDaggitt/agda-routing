open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; _≤_; _<_; z≤n; s≤s; zero; suc; _+_; _∸_) renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (≤-decTotalOrder; _<?_; ≤-refl; ≤-trans; n≤1+n; m≤m+n; <⇒≤; ≮⇒≥)
open import Data.List using (List; []; _∷_; length; concat; tabulate)
open import Data.List.Any.Membership.Propositional using () renaming (_∈_ to _∈ℕ_)
open import Data.List.Any.Membership.Propositional.Properties using ()
open import Data.Vec using (Vec; _∷_; fromList)
open import Data.Product using (∃; ∃₂; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary using (Setoid; Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong; sym)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Table using (Table; max; zipWith)
open import RoutingLib.Data.Table.Membership.Propositional.Properties using (max[t]∈t)
open import RoutingLib.Data.Nat.Properties using (ℕₛ; n≤0⇒n≡0; m≤n⇒m∸n≡0; module ≤-Reasoning)
open import RoutingLib.Data.List using (lookup)
open import RoutingLib.Data.List.Properties using (lookup-cong)
open import RoutingLib.Data.List.Membership.DecPropositional _≟ℕ_ using (deduplicate)
open import RoutingLib.Data.List.Membership.DecPropositional.Properties
  using (∈-deduplicate⁻; ∈-deduplicate⁺; ∈-concat⁺)
open import RoutingLib.Data.List.Sorting.Mergesort ≤-decTotalOrder
open import RoutingLib.Data.List.Sorting ≤-decTotalOrder using (Sorted)
open import RoutingLib.Data.List.Uniqueness.Propositional using (Unique)
open import RoutingLib.Data.List.Uniqueness.Propositional.Properties using (deduplicate!⁺)
open import RoutingLib.Asynchronous using (Parallelisation)
open import RoutingLib.Asynchronous.Theorems using (ACO; TrueUltrametricConditions)
open import RoutingLib.Function.Image using (FiniteImage)
open import RoutingLib.Function.Distance using (IsUltrametric)

module RoutingLib.Asynchronous.Theorems.MetricToBox
  {a ℓ n} {S : Fin n → Setoid a ℓ} {P : Parallelisation S}
  (𝓤𝓒 : TrueUltrametricConditions P) where

    open Parallelisation P using (M; f; Pred; _⊂_; _⊆_; _≈_; _≉_; _∈_; Singleton-t; ≈-refl; ≈-sym; ≈ᵢ-refl; ≈ᵢ-sym)
    open TrueUltrametricConditions 𝓤𝓒

    module _ {i} where

      open IsUltrametric (d-isUltrametric i) renaming
        ( sym to dᵢ-sym
        ; eq⇒0 to x≈y⇒dᵢ≡0
        ; 0⇒eq to dᵢ≡0⇒x≈y
        ; cong to dᵢ-cong
        ) public


    d-sym : ∀ x y → d x y ≡ d y x
    d-sym = {!!}

    d-cong : ∀ {m n p q} → m ≈ n → p ≈ q → d m p ≡ d n q
    d-cong = {!!}

    d≡0⇒x≈y : ∀ {x y} → d x y ≡ 0 → x ≈ y
    d≡0⇒x≈y = {!!}

    f-cong : ∀ {x y} → x ≈ y → f x ≈ f y
    f-cong = {!!}
    
    postulate x* : M

    postulate fx*≈x* : f x* ≈ x*
    --open FiniteImage (d-finiteImage x*)

{-
    allDistances : List ℕ
    allDistances = concat (tabulate (λ i → FiniteImage.image (d-finiteImage i (x* i))))

    allDistances-complete : ∀ i m → dᵢ (x* i) m ∈ℕ allDistances
    allDistances-complete i m = {!∈-concat⁺ ?!}
-}

    -- Radii in list form
{-
    radii : List ℕ
    radii = mergesort (deduplicate allDistances)

    radii↗ : Sorted radii
    radii↗ = mergesort↗ (deduplicate allDistances)
    
    radii! : Unique radii
    radii! = mergesort!⁺ (deduplicate!⁺ _≟ℕ_ allDistances)

    radii-complete : ∀ i m → dᵢ (x* i) m ∈ℕ radii
    radii-complete x i = {!!} --∈-mergesort⁺ (∈-deduplicate⁺ _≟ℕ_ (complete x))
-}
{-
    radiiₗ-sound : ∀ {r} → r ∈ℕ radiiₗ → ∃ λ x → d x* x ≡ r
    radiiₗ-sound r∈radii = sound (∈-deduplicate⁻ _≟ℕ_ (∈-mergesort⁻ r∈radii))
-}

    -- Total number of radii

    
    postulate nonZeroRadii : List ℕ

    T-1 : ℕ
    T-1 = length nonZeroRadii
    
    T : ℕ
    T = suc T-1


    T-1∸t<T : ∀ t → T-1 ∸ t < T
    T-1∸t<T = {!!}

    radii : List ℕ
    radii = zero ∷ nonZeroRadii

    postulate radii-mono-< : ∀ {s t} → s < t → (T-1∸s<T : T-1 ∸ s < T) (T-1∸t<T : T-1 ∸ t < T) →
                           lookup radii T-1∸t<T < lookup radii T-1∸s<T

    postulate radii-mono-≤ : ∀ {s t} → s ≤ t → (T-1∸s<T : T-1 ∸ s < T) (T-1∸t<T : T-1 ∸ t < T) →
                           lookup radii T-1∸t<T ≤ lookup radii T-1∸s<T
                           
    dx*m∈radii : ∀ m → ∃ λ k → d x* m ≡ lookup radii (T-1∸t<T k)
    dx*m∈radii = {!!}
    

    -- Radii functions
    
    r[_] : ℕ → ℕ
    r[ k ] = lookup radii (T-1∸t<T k)

    r-mono-≤ : ∀ {s t} → s ≤ t → r[ t ] ≤ r[ s ]
    r-mono-≤ = {!!}

    r-mono⁻¹-< : ∀ {s t} → r[ t ] < r[ s ] → s < t
    r-mono⁻¹-< = {!!}

    dx*m≡r[k] : ∀ m → ∃ λ k → d x* m ≡ r[ k ]
    dx*m≡r[k] = {!!}

    -- Definitions of the boxes D

    D : ℕ → Pred _
    D t i m = dᵢ (x* i) m ≤ r[ t ]

    -- D is decreasing
    
    D-decreasing : ∀ K → K < T → D (suc K) ⊆ D K
    D-decreasing K K<T {m} m∈D₁₊ₖ i = begin
      dᵢ (x* i) (m i)                ≤⟨ m∈D₁₊ₖ i ⟩
      lookup radii (T-1∸t<T (suc K)) ≤⟨ <⇒≤ (radii-mono-< ≤-refl _ _) ⟩
      lookup radii (T-1∸t<T K)       ∎
      where open ≤-Reasoning

    -- D is finishing
    
    m∈D[T+K]⇒x*≈m : ∀ K m → m ∈ D (T + K) → x* ≈ m
    m∈D[T+K]⇒x*≈m K m m∈D[T+K] i = dᵢ≡0⇒x≈y (n≤0⇒n≡0 (begin
      dᵢ (x* i) (m i)                ≤⟨ m∈D[T+K] i ⟩
      r[ T + K ]                     ≡⟨ lookup-cong radii (m≤n⇒m∸n≡0 (≤-trans (n≤1+n T-1) (m≤m+n T K))) _ (s≤s z≤n) ⟩
      lookup radii (s≤s z≤n)         ≡⟨⟩
      0 ∎))
      where open ≤-Reasoning
      
    x*∈D[T+K] : ∀ K → x* ∈ D (T + K)
    x*∈D[T+K] K i = subst (_≤ r[ T + K ]) (sym (x≈y⇒dᵢ≡0 ≈ᵢ-refl)) z≤n

    D-finish : ∃ λ ξ → ∀ K → Singleton-t ξ (D (T + K))
    D-finish = x* , λ K → (x*∈D[T+K] K , m∈D[T+K]⇒x*≈m K)

    test : ∀ K (x : M) → d x* x < r[ K ] → x ∈ D (suc K)
    test K x d[x*,x]<radiiᵢ[K] j with dx*m≡r[k] x
    ... | (S , dx*m≡r[S]) = ≤-trans {!!} dx*x≤r[1+k]
      where

      K<S : K < S
      K<S = r-mono⁻¹-< (subst (_< r[ K ]) dx*m≡r[S] d[x*,x]<radiiᵢ[K])

      dx*x≤r[1+k] : d x* x ≤ r[ suc K ]
      dx*x≤r[1+k] = subst (_≤ r[ suc K ]) (sym dx*m≡r[S]) (r-mono-≤ K<S)

      --dᵢx*

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
      d x* (f t)               ≡⟨ d-cong (≈-sym fx*≈x*) ≈-refl ⟩
      d (f x*) (f t)           <⟨ f-strContrOver-d t≉x* ⟩
      d x* t                   ≡⟨ d[x*,t]≡dⱼ[x*ⱼ,tⱼ] ⟩
      dᵢ (x* j) (t j)          ≤⟨ t∈D[K] j ⟩
      r[ K ]                   ∎) i
      where open ≤-Reasoning


    f-monotonic  : ∀ K {t} → t ∈ D K → f t ∈ D (suc K)
    f-monotonic K {t} with t ≟ x*
    ... | yes t≈x* = f-monotonic-x*≈ t≈x*
    ... | no  t≉x* = f-monotonic-x*≉ t≉x*
      
    D-subst : ∀ K {x y} → x ≈ y → x ∈ D K → y ∈ D K
    D-subst K {x} {y} x≈y x∈D[K] i = begin
      dᵢ (x* i) (y i)  ≡⟨ dᵢ-cong ≈ᵢ-refl (≈ᵢ-sym (x≈y i)) ⟩
      dᵢ (x* i) (x i)  ≤⟨ x∈D[K] i ⟩
      r[ K ]           ∎
      where open ≤-Reasoning


    aco : ACO P _
    aco = record
      { T            = T
      ; D            = D
      ; D-decreasing = D-decreasing
      ; D-finish     = D-finish
      ; f-monotonic  = f-monotonic
      ; D-subst      = D-subst
      }
