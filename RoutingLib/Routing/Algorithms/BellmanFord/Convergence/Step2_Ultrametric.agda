open import Level using () renaming (zero to lzero; _⊔_ to _⊔ₗ_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (DecTotalOrder; Setoid; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; subst) renaming (setoid to ≡-setoid; refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.Nat using (ℕ; suc; zero; z≤n; s≤s; decTotalOrder; _⊔_; _*_; _∸_; module ≤-Reasoning) renaming (_≤_ to _≤ℕ_; _<_ to _<ℕ_; _≟_ to _≟ℕ_)
open import Data.Nat.Properties using (n≤1+n; 1+n≰n; m≤m⊔n; ⊔-sel)
open import Data.List using ([]; _∷_; List; foldr; map)
open import Data.List.Properties using (map-cong)
open import Data.List.All using (All; []; _∷_) renaming (map to All-map; lookup to All-lookup)
open import Data.List.All.Properties using (map-All)
open import Data.List.Any as Any using (here; there)
open import Data.Product using (_×_; ∃₂; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import RoutingLib.Data.List.All.Properties using (map-preserves-predicates; forced-map)
open import RoutingLib.Data.List.Folds using (foldr-×preserves; foldr-forces×)
open import RoutingLib.Data.Nat.Properties using (⊔-comm; n≤m⊔n; ⊔-pres-≤; 0-idᵣ-⊔; m⊔n≡m⇨n≤m; o∸n≤o∸m∧m≤o⇨m≤n; n≤m⇨s[m]∸n≡s[n∸m]; <⇒≢; ⊔-×preserves-x≤; ⊔-preserves-≡x; ⊔-forces×-≤x; m<n⇨0<n∸m)
open import RoutingLib.Routing.Definitions
open import RoutingLib.Function.HeightFunction
open import RoutingLib.Data.List.Any.GenericMembership using (selective-foldr'; map-∈)
open import RoutingLib.Routing.Algorithms.DistributedBellmanFord.Convergence.SufficientConditions
open import RoutingLib.Function.Metric using (IsMetric; Metric; IsUltrametric; TriIneq; StrongTriIneq; weaken)

open DecTotalOrder decTotalOrder using () renaming (reflexive to ≤ℕ-reflexive; refl to ≤ℕ-refl; trans to ≤ℕ-trans; antisym to ≤ℕ-antisym; _≤?_ to _≤ℕ?_)

open import RoutingLib.Routing.Algorithms.DistributedBellmanFord.Convergence.Step1_HeightFunction

module RoutingLib.Routing.Algorithms.DistributedBellmanFord.Convergence.Step2_Ultrametric
  {a b ℓ n-1}
  (rp : RoutingProblem a b ℓ (suc n-1))
  (cc : ConvergenceConditions (RoutingProblem.ra rp))
  (bhf : BoundedHeightFunction (ConvergenceConditions.≤-poset cc)) 
  where
  
  open RoutingProblem rp
  open ConvergenceConditions cc
  open BoundedHeightFunction bhf


  private
    n : ℕ
    n = suc n-1

    ℕₛ : Setoid lzero lzero
    ℕₛ = ≡-setoid ℕ


  ----------------------------------------
  -- Constructing the distance function --
  ----------------------------------------
  -- Using the height function over Route, we can now generate 
  -- a distance function over the RMatrices

  -- maximum distance value
  H : ℕ
  H = suc hₘₐₓ

  abstract

    -- an intermediate helper function
    dₕ : Route → Route → ℕ
    dₕ x y = (H ∸ h x) ⊔ (H ∸ h y)

    -- measures the distance between two routes 
    dₑ : Route → Route → ℕ
    dₑ x y with x ≟ y
    ... | yes _ = zero
    ... | no  _ = dₕ x y

    -- collates all the elementwise similarities between two matrices
    allDistances : RMatrix → RMatrix → List ℕ
    allDistances X Y = map (λ {(i , j) → dₑ (X i j) (Y i j)}) srcDstPairs

    -- the overall similarity between two iterations
    d : RMatrix → RMatrix → ℕ
    d X Y = foldr _⊔_ zero (allDistances X Y)

    ----------------
    -- Properties --
    ----------------
    -- Proof that the functions above have the required properties to
    -- be a similarity function

    h≤H : ∀ {x} → h x ≤ℕ H
    h≤H {x} = ≤ℕ-trans h≤hₘₐₓ (n≤1+n hₘₐₓ)

    0<H∸h : ∀ {x} → 0 <ℕ H ∸ h x 
    0<H∸h = m<n⇨0<n∸m (s≤s h≤hₘₐₓ)

    0<dₕ : ∀ {x y} → 0 <ℕ dₕ x y
    0<dₕ = ⊔-×preserves-x≤ 0<H∸h 0<H∸h

    dₕ-sym : ∀ x y → dₕ x y ≡ dₕ y x
    dₕ-sym x y = ⊔-comm (H ∸ h x) (H ∸ h y)

    dₕ-cong₂ : dₕ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
    dₕ-cong₂ x≈y u≈v = cong₂ _⊔_ (cong (H ∸_) (h-resp-≈ x≈y)) (cong (H ∸_) (h-resp-≈ u≈v))

    dₕ-strongTriIneq : StrongTriIneq S dₕ
    dₕ-strongTriIneq x y z = ⊔-pres-≤ (m≤m⊔n (H ∸ h x) (H ∸ h y)) (n≤m⊔n (H ∸ h y) (H ∸ h z))


    -- Elementwise similarity

    x≈y⇨dₑ≡0 : ∀ {x y} → x ≈ y → dₑ x y ≡ 0
    x≈y⇨dₑ≡0 {x} {y} x≈y with x ≟ y
    ... | yes _    = ≡-refl
    ... | no  xᵢⱼ≉yᵢⱼ = contradiction x≈y xᵢⱼ≉yᵢⱼ

    dₑ≡0⇨x≈y : ∀ {x y} → dₑ x y ≡ 0 → x ≈ y
    dₑ≡0⇨x≈y {x} {y} dₑ≡0 with x ≟ y 
    ... | yes x≈y = x≈y
    ... | no  _   = contradiction (≡-sym dₑ≡0) (<⇒≢ 0<dₕ)

    x≉y⇨H∸hx≤dₑ : ∀ {x y} → x ≉ y → H ∸ h x ≤ℕ dₑ x y
    x≉y⇨H∸hx≤dₑ {x} {y} x≉y with x ≟ y
    ... | yes x≈y = contradiction x≈y x≉y
    ... | no  _   = m≤m⊔n (H ∸ h x) (H ∸ h y)

    dₑ≡H∸hx⇨hx≤hy : ∀ {x y} → dₑ x y ≡ H ∸ h x → h x ≤ℕ h y
    dₑ≡H∸hx⇨hx≤hy {x} {y} dₑ≡H∸hx with x ≟ y
    ... | yes x≈y = contradiction (≡-trans dₑ≡H∸hx (n≤m⇨s[m]∸n≡s[n∸m] h≤hₘₐₓ)) λ()
    ... | no  x≉y = o∸n≤o∸m∧m≤o⇨m≤n (m⊔n≡m⇨n≤m dₑ≡H∸hx) h≤H

    dₑxy=hx⊎hy : ∀ {x y} → x ≉ y → (dₑ x y ≡ H ∸ h x) ⊎ (dₑ x y ≡ H ∸ h y)
    dₑxy=hx⊎hy {x} {y} x≉y with x ≟ y
    ... | yes x≈y = contradiction x≈y x≉y
    ... | no  _   = ⊔-sel (H ∸ h x) (H ∸ h y)

    0<dₑ⇨x≉y : ∀ {x y} → 0 <ℕ dₑ x y → x ≉ y
    0<dₑ⇨x≉y {x} {y} 0<dₑ with x ≟ y 
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

    dₑ-strongTriIneq : StrongTriIneq S dₑ
    dₑ-strongTriIneq x y z with x ≟ y | y ≟ z | x ≟ z
    ... | _       | _       | yes _  = z≤n
    ... | yes x≈y | yes y≈z | no x≉z = contradiction (trans x≈y y≈z) x≉z
    ... | yes x≈y | no  _   | no _   = subst (dₕ x z ≤ℕ_) (dₕ-cong₂ x≈y refl) ≤ℕ-refl
    ... | no  _   | yes y≈z | no _   = subst (_≤ℕ dₕ x y ⊔ 0) (≡-trans (⊔-comm (dₕ x y) 0) (dₕ-cong₂ refl y≈z)) ≤ℕ-refl
    ... | no  _   | no  _   | no _   = dₕ-strongTriIneq x y z


    -- All similarities

    0≤allSimilarities : ∀ X Y → All (0 ≤ℕ_) (allDistances X Y)
    0≤allSimilarities X Y = map-preserves-predicates (λ _ → z≤n) srcDstPairs

    X≈Y⇨alldistances≡0 : ∀ {X} {Y} → X ≈ₘ Y → All (_≡ 0) (allDistances X Y)
    X≈Y⇨alldistances≡0 {X} {Y} X≈Y = map-preserves-predicates (λ {(i , j) → x≈y⇨dₑ≡0 (X≈Y i j)}) srcDstPairs


    -- Similarity

    d-sym : ∀ X Y → d X Y ≡ d Y X
    d-sym X Y = cong (foldr _⊔_ 0) (map-cong (λ {(i , j) → dₑ-sym (X i j) (Y i j)}) srcDstPairs)

    dₑ≤d : ∀ X Y i j → dₑ (X i j) (Y i j) ≤ℕ d X Y
    dₑ≤d X Y i j = All-lookup (map-All (foldr-forces× {P = _≤ℕ d X Y} ⊔-forces×-≤x 0 (allDistances X Y) ≤ℕ-refl)) (∈-srcDstPairs (i , j))

    Xᵢⱼ≉Yᵢⱼ⇨H∸hXᵢⱼ≤d : ∀ {X Y i j} → X i j ≉ Y i j → H ∸ h (X i j) ≤ℕ d X Y 
    Xᵢⱼ≉Yᵢⱼ⇨H∸hXᵢⱼ≤d {X} {Y} {i} {j} Xᵢⱼ≉Yᵢⱼ = ≤ℕ-trans (x≉y⇨H∸hx≤dₑ Xᵢⱼ≉Yᵢⱼ) (dₑ≤d X Y i j)

    X≈Y⇨d≡0 : ∀ {X Y} → X ≈ₘ Y → d X Y ≡ 0
    X≈Y⇨d≡0 {X} {Y} X≈Y = foldr-×preserves ⊔-preserves-≡x  (X≈Y⇨alldistances≡0 X≈Y) ≡-refl

    d≡0⇨X≈Y : ∀ {X Y} → d X Y ≡ 0 → X ≈ₘ Y
    d≡0⇨X≈Y {X} {Y} d≡0 i j  = dₑ≡0⇨x≈y (≤ℕ-antisym (subst (dₑ (X i j) (Y i j) ≤ℕ_) d≡0 (dₑ≤d X Y i j)) z≤n)

    d≡dₑ : ∀ X Y → ∃₂ λ i j → d X Y ≡ dₑ (X i j) (Y i j)
    d≡dₑ X Y with selective-foldr' ℕₛ ⊔-sel 0 (allDistances X Y)
    ... | here d≡0 = fzero , fzero , (≡-trans d≡0 (≡-sym (x≈y⇨dₑ≡0 (d≡0⇨X≈Y d≡0 fzero fzero))))
    ... | there d∈allDistances with map-∈ ℕₛ F×Fₛ d∈allDistances
    ...   | (i , j) , _ , d≡dₑXᵢⱼYᵢⱼ = i , j , d≡dₑXᵢⱼYᵢⱼ

    d-strongTriIneq : StrongTriIneq Sₘ d
    d-strongTriIneq X Y Z with d≡dₑ X Z
    ... | i , j , dˣᶻ≡ij = 
      begin
        d X Z
      ≡⟨ dˣᶻ≡ij ⟩
        dₑ (X i j) (Z i j)
      ≤⟨ dₑ-strongTriIneq (X i j) (Y i j) (Z i j) ⟩
        dₑ (X i j) (Y i j) ⊔ dₑ (Y i j) (Z i j)
      ≤⟨ ⊔-pres-≤ (dₑ≤d X Y i j) (dₑ≤d Y Z i j) ⟩
        d X Y ⊔ d Y Z
      ∎
      where open ≤-Reasoning


  -----------------
  -- Ultrametric --
  -----------------
  -- We have now shown that d is an ultrametric

  d-isMetric : IsMetric Sₘ d
  d-isMetric = record { 
      eq⇨0 = X≈Y⇨d≡0 ; 
      0⇨eq = d≡0⇨X≈Y ; 
      sym = d-sym ; 
      triIneq = weaken Sₘ d-strongTriIneq 
    }

  d-metric : Metric Sₘ
  d-metric = record { 
      d = d ; 
      isMetric = d-isMetric 
    }

  d-isUltrametric : IsUltrametric Sₘ d
  d-isUltrametric = record { 
      isMetric = d-isMetric;
      strongTriIneq = d-strongTriIneq 
    }
