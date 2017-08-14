open import Level using () renaming (zero to lzero; _⊔_ to _⊔ₗ_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (DecTotalOrder; Setoid; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; cong₂; subst; subst₂) renaming (setoid to ≡-setoid; refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_)
open import Data.Nat using (ℕ; suc; zero; z≤n; s≤s; decTotalOrder; _⊔_; _*_; _∸_; module ≤-Reasoning) renaming (_≤_ to _≤ℕ_; _≥_ to _≥ℕ_; _<_ to _<ℕ_; _≟_ to _≟ℕ_)
open import Data.Nat.Properties using (n≤1+n; 1+n≰n; m≤m⊔n; ⊔-sel; n∸m≤n; ≤-step; ∸-mono; +-∸-assoc)
open import Data.List using ([]; _∷_; List; foldr; map; zipWith)
open import Data.List.Properties using (map-cong)
open import Data.List.All using (All; []; _∷_) renaming (map to All-map; lookup to All-lookup; tabulate to All-tabulate)
open import Data.List.All.Properties using (map-All)
open import Data.List.Any as Any using (here; there)
open import Data.Product using (_×_; ∃₂; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)

open import RoutingLib.Data.List using (max; allFinPairs)
open import RoutingLib.Data.List.Properties using (foldr-×preserves; foldr-forces×; max[xs]≤x; max[xs]≡x)
open import RoutingLib.Data.List.All.Properties using (All-map⁺₂)
open import RoutingLib.Data.Nat.Properties using (ℕₛ; ⊔-comm; n≤m⊔n; ⊔-mono-≤; 0-idᵣ-⊔; m⊔n≡m⇒n≤m; o∸n≤o∸m∧m≤o⇒m≤n; m<n⇒n≡1+o; <⇒≤; <⇒≢; ⊔-preserves-≡x; ⊔-forces×-≤x; ⊔-×preserves-≤x; ⊔-⊎preservesₗ-x≤; m<n⇒0<n∸m; n≤m⇒m⊔n≡m) renaming (≤-reflexive to ≤ℕ-reflexive; ≤-refl to ≤ℕ-refl; ≤-trans to ≤ℕ-trans; ≤-antisym to ≤ℕ-antisym)
open import RoutingLib.Routing.Definitions using (RoutingProblem; RoutingAlgebra)
open import RoutingLib.Data.List.Membership.Properties using (∈-map⁻; foldr-∈)
open import RoutingLib.Data.List.Membership.Propositional using (_∈_; ∈-map⁺; ∈-allFinPairs⁺)
open import RoutingLib.Function.Distance using (IsUltrametric; MaxTriangleIneq)

open import RoutingLib.Routing.BellmanFord.GeneralConvergence.SufficientConditions

module RoutingLib.Routing.BellmanFord.GeneralConvergence.Step2_Ultrametric
  {a b ℓ n-1}
  {𝓡𝓐 : RoutingAlgebra a b ℓ}
  (𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1)) 
  (sc : SufficientConditions 𝓡𝓐)
  where
  
  open import RoutingLib.Routing.BellmanFord.GeneralConvergence.Step1_HeightFunction 𝓡𝓟 sc
  
  open RoutingProblem 𝓡𝓟
  open SufficientConditions sc
  

  private
    n : ℕ
    n = suc n-1

    𝔽²ₛ : Setoid lzero lzero
    𝔽²ₛ = ≡-setoid (Fin n × Fin n)

  ----------------------------------------
  -- Constructing the distance function --
  ----------------------------------------
  -- Using the height function over Route, we can now generate 
  -- a distance function over the RMatrices

  -- maximum distance value
  dₘₐₓ : ℕ
  dₘₐₓ = hₘₐₓ

  dₛᵤₚ : ℕ
  dₛᵤₚ = suc dₘₐₓ
  
  abstract

    -- an intermediate helper function
    dₕ : Route → Route → ℕ
    dₕ x y = (dₛᵤₚ ∸ h x) ⊔ (dₛᵤₚ ∸ h y)

    -- the elementwise distance measures the distance between two routes 
    dₑ : Route → Route → ℕ
    dₑ x y with x ≟ y
    ... | yes _ = zero
    ... | no  _ = dₕ x y

    -- collates all the elementwise distances between two matrices
    allDistances : RMatrix → RMatrix → List ℕ
    allDistances X Y = map (λ {(i , j) → dₑ (X i j) (Y i j)}) (allFinPairs n)

    -- the overall distance between two iterations
    d : RMatrix → RMatrix → ℕ
    d X Y = max 0 (allDistances X Y)

    ----------------
    -- Properties --
    ----------------
    -- Proof that the functions above have the required properties to
    -- be a similarity function

    h≤dₛᵤₚ : ∀ {x} → h x ≤ℕ dₛᵤₚ
    h≤dₛᵤₚ = ≤ℕ-trans h≤hₘₐₓ (n≤1+n hₘₐₓ)

    0<dₘₐₓ∸h : ∀ {x} → 0 <ℕ (suc dₘₐₓ ∸ h x) 
    0<dₘₐₓ∸h = m<n⇒0<n∸m (s≤s h≤hₘₐₓ)

    dₛᵤₚ∸h≤dₘₐₓ : ∀ {x} → (suc dₘₐₓ) ∸ h x ≤ℕ dₘₐₓ
    dₛᵤₚ∸h≤dₘₐₓ {x} with m<n⇒n≡1+o (1≤h x)
    ... | (o , h≡1+o) = subst (λ v → dₛᵤₚ ∸ v ≤ℕ dₘₐₓ) (≡-sym h≡1+o) (n∸m≤n o dₘₐₓ)

    -- dₕ

    0<dₕ : ∀ {x y} → 0 <ℕ dₕ x y
    0<dₕ = ⊔-⊎preservesₗ-x≤ _ 0<dₘₐₓ∸h

    dₕ<dₘₐₓ : ∀ x y → dₕ x y ≤ℕ dₘₐₓ
    dₕ<dₘₐₓ x y = ⊔-×preserves-≤x dₛᵤₚ∸h≤dₘₐₓ dₛᵤₚ∸h≤dₘₐₓ
    
    dₕ-sym : ∀ x y → dₕ x y ≡ dₕ y x
    dₕ-sym x y = ⊔-comm (dₛᵤₚ ∸ h x) (dₛᵤₚ ∸ h y)

    dₕ-cong₂ : dₕ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
    dₕ-cong₂ x≈y u≈v = cong₂ _⊔_ (cong (dₛᵤₚ ∸_) (h-resp-≈ x≈y)) (cong (dₛᵤₚ ∸_) (h-resp-≈ u≈v))

    dₕ-mono-≤ : dₕ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≥ℕ_
    dₕ-mono-≤ x≤y u≤v = ⊔-mono-≤ (∸-mono ≤ℕ-refl (h-resp-≤ x≤y)) (∸-mono ≤ℕ-refl (h-resp-≤ u≤v))
    
    dₕ-maxTriIneq : MaxTriangleIneq S dₕ
    dₕ-maxTriIneq x y z = ⊔-mono-≤ (m≤m⊔n (dₛᵤₚ ∸ h x) (dₛᵤₚ ∸ h y)) (n≤m⊔n (dₛᵤₚ ∸ h y) (dₛᵤₚ ∸ h z))


    -- Elementwise distance

    dₑ≤dₘₐₓ : ∀ x y → dₑ x y ≤ℕ dₘₐₓ
    dₑ≤dₘₐₓ x y with x ≟ y
    ... | yes _ = z≤n
    ... | no  _ = dₕ<dₘₐₓ x y

    x≈y⇒dₑ≡0 : ∀ {x y} → x ≈ y → dₑ x y ≡ 0
    x≈y⇒dₑ≡0 {x} {y} x≈y with x ≟ y
    ... | yes _    = ≡-refl
    ... | no  xᵢⱼ≉yᵢⱼ = contradiction x≈y xᵢⱼ≉yᵢⱼ

    dₑ≡0⇒x≈y : ∀ {x y} → dₑ x y ≡ 0 → x ≈ y
    dₑ≡0⇒x≈y {x} {y} dₑ≡0 with x ≟ y 
    ... | yes x≈y = x≈y
    ... | no  _   = contradiction (≡-sym dₑ≡0) (<⇒≢ 0<dₕ)

    x≉y⇒dₛᵤₚ∸hx≤dₑ : ∀ {x y} → x ≉ y → dₛᵤₚ ∸ h x ≤ℕ dₑ x y
    x≉y⇒dₛᵤₚ∸hx≤dₑ {x} {y} x≉y with x ≟ y
    ... | yes x≈y = contradiction x≈y x≉y
    ... | no  _   = m≤m⊔n (dₛᵤₚ ∸ h x) (dₛᵤₚ ∸ h y)

    dₑ≡dₛᵤₚ∸hx⇒hx≤hy : ∀ {x y} → dₑ x y ≡ dₛᵤₚ ∸ h x → h x ≤ℕ h y
    dₑ≡dₛᵤₚ∸hx⇒hx≤hy {x} {y} dₑ≡dₘₐₓ∸hx with x ≟ y
    ... | yes x≈y = contradiction (≡-trans dₑ≡dₘₐₓ∸hx (+-∸-assoc 1 h≤hₘₐₓ)) λ()
    ... | no  x≉y = o∸n≤o∸m∧m≤o⇒m≤n (m⊔n≡m⇒n≤m dₑ≡dₘₐₓ∸hx) h≤dₛᵤₚ

    hx≤hy⇒dₑ≡dₛᵤₚ∸hx : ∀ {x y} → h x <ℕ h y → dₑ x y ≡ dₛᵤₚ ∸ h x
    hx≤hy⇒dₑ≡dₛᵤₚ∸hx {x} {y} hx<hy with x ≟ y
    ... | yes x≈y = contradiction (h-resp-≈ x≈y) (<⇒≢ hx<hy)
    ... | no  x≉y = n≤m⇒m⊔n≡m (∸-mono (≤ℕ-refl {dₛᵤₚ}) (<⇒≤ hx<hy))
    
    dₑxy=hx⊎hy : ∀ {x y} → x ≉ y → (dₑ x y ≡ dₛᵤₚ ∸ h x) ⊎ (dₑ x y ≡ dₛᵤₚ ∸ h y)
    dₑxy=hx⊎hy {x} {y} x≉y with x ≟ y
    ... | yes x≈y = contradiction x≈y x≉y
    ... | no  _   = ⊔-sel (dₛᵤₚ ∸ h x) (dₛᵤₚ ∸ h y)

    0<dₑ⇒x≉y : ∀ {x y} → 0 <ℕ dₑ x y → x ≉ y
    0<dₑ⇒x≉y {x} {y} 0<dₑ with x ≟ y 
    ... | yes x≈yⱼ = contradiction 0<dₑ 1+n≰n 
    ... | no  x≉y = x≉y

    dₑ-sym : ∀ x y → dₑ x y ≡ dₑ y x
    dₑ-sym x y with x ≟ y | y ≟ x
    ... | yes _   | yes _   = ≡-refl
    ... | no  x≉y | yes y≈x = contradiction (sym y≈x) x≉y 
    ... | yes x≈y | no  y≉x = contradiction (sym x≈y) y≉x 
    ... | no  _   | no  _   = dₕ-sym x y

    dₑ-cong₂ : dₑ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
    dₑ-cong₂ {x} {y} {u} {v} x≈y u≈v with x ≟ u | y ≟ v
    ... | yes _   | yes _   = ≡-refl
    ... | yes x≈u | no  y≉v = contradiction (trans (trans (sym x≈y) x≈u) u≈v) y≉v
    ... | no  x≉u | yes y≈v = contradiction (trans (trans x≈y y≈v) (sym u≈v)) x≉u
    ... | no  _   | no  _   = dₕ-cong₂ x≈y u≈v

    dₑ-maxTriIneq : MaxTriangleIneq S dₑ
    dₑ-maxTriIneq x y z with x ≟ y | y ≟ z | x ≟ z
    ... | _       | _       | yes _  = z≤n
    ... | yes x≈y | yes y≈z | no x≉z = contradiction (trans x≈y y≈z) x≉z
    ... | yes x≈y | no  _   | no _   = subst (dₕ x z ≤ℕ_) (dₕ-cong₂ x≈y refl) ≤ℕ-refl
    ... | no  _   | yes y≈z | no _   = subst (_≤ℕ dₕ x y ⊔ 0) (≡-trans (⊔-comm (dₕ x y) 0) (dₕ-cong₂ refl y≈z)) ≤ℕ-refl
    ... | no  _   | no  _   | no _   = dₕ-maxTriIneq x y z


    -- All distances

    0≤allDistances : ∀ X Y → All (0 ≤ℕ_) (allDistances X Y)
    0≤allDistances X Y = All-map⁺₂ (λ _ → z≤n) (allFinPairs n)

    allDistances≤dₘₐₓ : ∀ X Y → All (_≤ℕ dₘₐₓ) (allDistances X Y)
    allDistances≤dₘₐₓ X Y = All-map⁺₂ (λ {(i , j) → dₑ≤dₘₐₓ (X i j) (Y i j)}) (allFinPairs n)

    X≈Y⇒alldistances≡0 : ∀ {X} {Y} → X ≈ₘ Y → All (_≡ 0) (allDistances X Y)
    X≈Y⇒alldistances≡0 {X} {Y} X≈Y = All-map⁺₂ (λ {(i , j) → x≈y⇒dₑ≡0 (X≈Y i j)}) (allFinPairs n)

    allDistances-cong₂ : allDistances Preserves₂ _≈ₘ_ ⟶ _≈ₘ_ ⟶ _≡_
    allDistances-cong₂ X≈Y U≈V = map-cong (λ {(i , j) → dₑ-cong₂ (X≈Y i j) (U≈V i j)}) (allFinPairs n)

    allDistances-sym : ∀ X Y → allDistances X Y ≡ allDistances Y X
    allDistances-sym X Y = map-cong (λ {(i , j) → dₑ-sym (X i j) (Y i j)}) (allFinPairs n)

    allDistances≤d : ∀ X Y → All (_≤ℕ d X Y) (allDistances X Y)
    allDistances≤d X Y = foldr-forces× ⊔-forces×-≤x 0 (allDistances X Y) ≤ℕ-refl

    ∈-allDistances : ∀ X Y i j → dₑ (X i j) (Y i j) ∈ allDistances X Y
    ∈-allDistances X Y i j = ∈-map⁺ (λ {(i , j) → dₑ (X i j) (Y i j)}) (∈-allFinPairs⁺ i j)

    -- Similarity

    d-sym : ∀ X Y → d X Y ≡ d Y X
    d-sym X Y = cong (max 0) (allDistances-sym X Y)

    d-cong₂ : d Preserves₂ _≈ₘ_ ⟶ _≈ₘ_ ⟶ _≡_
    d-cong₂ X≈Y U≈V = cong (max 0) (allDistances-cong₂ X≈Y U≈V)
    
    dₑ≤d : ∀ X Y i j → dₑ (X i j) (Y i j) ≤ℕ d X Y
    dₑ≤d X Y i j = All-lookup (map-All (allDistances≤d X Y)) (∈-allFinPairs⁺ i j)

    d≤dₘₐₓ : ∀ X Y → d X Y ≤ℕ dₘₐₓ
    d≤dₘₐₓ X Y = max[xs]≤x (allDistances≤dₘₐₓ X Y) z≤n

    d<dₛᵤₚ : ∀ X Y → d X Y <ℕ dₛᵤₚ
    d<dₛᵤₚ X Y = s≤s (d≤dₘₐₓ X Y)
    
    d≤dₛᵤₚ : ∀ X Y → d X Y ≤ℕ dₛᵤₚ
    d≤dₛᵤₚ X Y = <⇒≤ (d<dₛᵤₚ X Y)
    
    Xᵢⱼ≉Yᵢⱼ⇒dₛᵤₚ∸hXᵢⱼ≤d : ∀ {X Y i j} → X i j ≉ Y i j → dₛᵤₚ ∸ h (X i j) ≤ℕ d X Y 
    Xᵢⱼ≉Yᵢⱼ⇒dₛᵤₚ∸hXᵢⱼ≤d {X} {Y} {i} {j} Xᵢⱼ≉Yᵢⱼ = ≤ℕ-trans (x≉y⇒dₛᵤₚ∸hx≤dₑ Xᵢⱼ≉Yᵢⱼ) (dₑ≤d X Y i j)

    Xᵢⱼ≉Yᵢⱼ⇒dₛᵤₚ∸hYᵢⱼ≤d : ∀ {X Y i j} → X i j ≉ Y i j → dₛᵤₚ ∸ h (Y i j) ≤ℕ d X Y
    Xᵢⱼ≉Yᵢⱼ⇒dₛᵤₚ∸hYᵢⱼ≤d {X} {Y} Xᵢⱼ≉Yᵢⱼ = subst (_ ≤ℕ_) (d-sym Y X) (Xᵢⱼ≉Yᵢⱼ⇒dₛᵤₚ∸hXᵢⱼ≤d (Xᵢⱼ≉Yᵢⱼ ∘ sym))
    
    X≈Y⇒d≡0 : ∀ {X Y} → X ≈ₘ Y → d X Y ≡ 0
    X≈Y⇒d≡0 {X} {Y} X≈Y = foldr-×preserves ⊔-preserves-≡x (X≈Y⇒alldistances≡0 X≈Y) ≡-refl

    d≡0⇒X≈Y : ∀ {X Y} → d X Y ≡ 0 → X ≈ₘ Y
    d≡0⇒X≈Y {X} {Y} d≡0 i j = dₑ≡0⇒x≈y (≤ℕ-antisym (subst (dₑ (X i j) (Y i j) ≤ℕ_) d≡0 (dₑ≤d X Y i j)) z≤n)

    d≡dₑ : ∀ X Y → ∃₂ λ i j → d X Y ≡ dₑ (X i j) (Y i j)
    d≡dₑ X Y with foldr-∈ ℕₛ ⊔-sel 0 (allDistances X Y)
    ... | inj₁ d≡0 = fzero , fzero , (≡-trans d≡0 (≡-sym (x≈y⇒dₑ≡0 (d≡0⇒X≈Y d≡0 fzero fzero))))
    ... | inj₂ d∈allDistances with ∈-map⁻ 𝔽²ₛ ℕₛ d∈allDistances
    ...   | (i , j) , _ , d≡dₑXᵢⱼYᵢⱼ = i , j , d≡dₑXᵢⱼYᵢⱼ

    d≡dₛᵤₚ∸Xᵢⱼ : ∀ {X Y i j} → (∀ k l → dₑ (X k l) (Y k l) ≤ℕ dₑ (X i j) (Y i j)) → h (X i j) <ℕ h (Y i j) → d X Y ≡ dₛᵤₚ ∸ h (X i j) 
    d≡dₛᵤₚ∸Xᵢⱼ {X} {Y} {i} {j} dₑₖₗ≤dₑᵢⱼ hXᵢⱼ<hYᵢⱼ = max[xs]≡x (subst (_∈ _) (hx≤hy⇒dₑ≡dₛᵤₚ∸hx hXᵢⱼ<hYᵢⱼ) (∈-allDistances X Y i j)) (All-map⁺₂ (λ {(k , l) → subst (_ ≤ℕ_) (hx≤hy⇒dₑ≡dₛᵤₚ∸hx hXᵢⱼ<hYᵢⱼ) (dₑₖₗ≤dₑᵢⱼ k l)}) (allFinPairs n)) z≤n

    d≡dₛᵤₚ∸Yᵢⱼ : ∀ {X Y i j} → (∀ k l → dₑ (X k l) (Y k l) ≤ℕ dₑ (X i j) (Y i j)) → h (Y i j) <ℕ h (X i j) → d X Y ≡ dₛᵤₚ ∸ h (Y i j)
    d≡dₛᵤₚ∸Yᵢⱼ dₑₖₗ≤dₑᵢⱼ hYᵢⱼ<hXᵢⱼ = ≡-trans (d-sym _ _) (d≡dₛᵤₚ∸Xᵢⱼ (λ k l → subst₂ _≤ℕ_ (dₑ-sym _ _) (dₑ-sym _ _) (dₑₖₗ≤dₑᵢⱼ k l)) hYᵢⱼ<hXᵢⱼ)

    d-maxTriIneq : MaxTriangleIneq ℝ𝕄ₛ d
    d-maxTriIneq X Y Z with d≡dₑ X Z
    ... | i , j , dˣᶻ≡ij = 
      begin
        d X Z                                   ≡⟨ dˣᶻ≡ij ⟩
        dₑ (X i j) (Z i j)                      ≤⟨ dₑ-maxTriIneq (X i j) (Y i j) (Z i j) ⟩
        dₑ (X i j) (Y i j) ⊔ dₑ (Y i j) (Z i j) ≤⟨ ⊔-mono-≤ (dₑ≤d X Y i j) (dₑ≤d Y Z i j) ⟩
        d X Y ⊔ d Y Z
      ∎
      where open ≤-Reasoning

    d-findWorstDisagreement : ∀ {X Y} → X ≉ₘ Y 
                              → ∃₂ λ i j 
                                 → X i j ≉ Y i j
                                   × d X Y ≡ dₑ (X i j) (Y i j)
                                   × (dₑ (X i j) (Y i j) ≡ dₛᵤₚ ∸ h (X i j) ⊎ dₑ (X i j) (Y i j) ≡ dₛᵤₚ ∸ h (Y i j))
    d-findWorstDisagreement {X} {Y} X≉Y with d X Y ≟ℕ 0 | d≡dₑ X Y 
    ... | yes d≡0 | _ = contradiction (d≡0⇒X≈Y d≡0) X≉Y
    ... | no  d≢0 | i , j , d≡dₑXᵢⱼYᵢⱼ with λ Xᵢⱼ≈Yᵢⱼ → d≢0 (≡-trans d≡dₑXᵢⱼYᵢⱼ (x≈y⇒dₑ≡0 Xᵢⱼ≈Yᵢⱼ))
    ...   | Xᵢⱼ≉Yᵢⱼ  = i , j , Xᵢⱼ≉Yᵢⱼ , d≡dₑXᵢⱼYᵢⱼ , dₑxy=hx⊎hy Xᵢⱼ≉Yᵢⱼ
    
    -----------------
    -- Ultrametric --
    -----------------
    -- We have now shown that d is an ultrametric

    d-isUltrametric : IsUltrametric ℝ𝕄ₛ d
    d-isUltrametric = record 
      { eq⇒0        = X≈Y⇒d≡0 
      ; 0⇒eq        = d≡0⇒X≈Y 
      ; sym         = d-sym 
      ; maxTriangle = d-maxTriIneq 
      }
