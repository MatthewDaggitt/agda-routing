open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (DecTotalOrder; Setoid; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_)
open import Data.Nat using (ℕ; suc; zero; z≤n; s≤s; _⊔_; _*_; _∸_) renaming (_≤_ to _≤ℕ_; _≥_ to _≥ℕ_; _<_ to _<ℕ_; _≟_ to _≟ℕ_)
open import Data.Nat.Properties using (n≤1+n; 1+n≰n; m≤m⊔n; <⇒≤; <⇒≢;  ⊔-sel; ⊔-comm; ⊔-identityʳ; n≤m⊔n; ⊔-mono-≤; n∸m≤n; ≤-step; ∸-mono; +-∸-assoc; n∸n≡0; module ≤-Reasoning) renaming (≤-reflexive to ≤ℕ-reflexive; ≤-refl to ≤ℕ-refl; ≤-trans to ≤ℕ-trans; ≤-antisym to ≤ℕ-antisym)
open import Data.Product using (∃₂;_×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)

open import RoutingLib.Data.Nat.Properties using (ℕₛ; m⊔n≡m⇒n≤m; o∸n≤o∸m∧m≤o⇒m≤n; m<n⇒n≡1+o; ⊔-preserves-≡x; n⊔o≤m⇒n≤m×o≤m; n≤m×o≤m⇒n⊔o≤m; m≤n⇒m≤n⊔o; m<n⇒0<n∸m; n≤m⇒m⊔n≡m; m≤n⇒m⊔n≡n; ∸-cancelˡ)
open import RoutingLib.Function.Distance using (IsUltrametric; MaxTriangleIneq)
open import RoutingLib.Data.Matrix using (Matrix; zipWith; max⁺)
open import RoutingLib.Data.Matrix.Properties using (max⁺-cong; M≤max⁺[M]; max⁺[M]≡x; max⁺[M]≤x; max⁺-constant; zipWith-sym)
open import RoutingLib.Data.Matrix.Membership.Propositional.Properties using (max⁺[M]∈M)
open import RoutingLib.Data.Matrix.Relation.Pointwise using (zipWith-cong)

open import RoutingLib.Routing.Definitions using (RoutingProblem; RoutingAlgebra)
open import RoutingLib.Routing.BellmanFord.GeneralConvergence.SufficientConditions
import RoutingLib.Routing.BellmanFord.GeneralConvergence.Step1_HeightFunction as Step1

module RoutingLib.Routing.BellmanFord.GeneralConvergence.Step2_Ultrametric
  {a b ℓ n-1}
  {𝓡𝓐 : RoutingAlgebra a b ℓ}
  (𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1)) 
  (𝓢𝓒 : SufficientConditions 𝓡𝓐)
  where
  
  open RoutingProblem 𝓡𝓟
  open SufficientConditions 𝓢𝓒
  
  open Step1 𝓡𝓟 𝓢𝓒

  private
    n : ℕ
    n = suc n-1

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

    -- the overall distance between two iterations
    d : RMatrix → RMatrix → ℕ
    d X Y = max⁺ (zipWith dₑ X Y)

    ----------------
    -- Properties --
    ----------------
    -- Proof that the functions above have the required properties to
    -- be a similarity function

    h≤dₛᵤₚ : ∀ {x} → h x ≤ℕ dₛᵤₚ
    h≤dₛᵤₚ = ≤ℕ-trans h≤hₘₐₓ (n≤1+n hₘₐₓ)

    0<dₛᵤₚ∸h : ∀ {x} → 0 <ℕ dₛᵤₚ ∸ h x
    0<dₛᵤₚ∸h = m<n⇒0<n∸m (s≤s h≤hₘₐₓ)

    dₛᵤₚ∸h≤dₘₐₓ : ∀ {x} → (suc dₘₐₓ) ∸ h x ≤ℕ dₘₐₓ
    dₛᵤₚ∸h≤dₘₐₓ {x} with m<n⇒n≡1+o (1≤h x)
    ... | (o , h≡1+o) rewrite h≡1+o = n∸m≤n o hₘₐₓ

    dₛᵤₚ∸hx≡1⇒x≈0 : ∀ {x} → dₛᵤₚ ∸ h x ≡ 1 → x ≈ 0#
    dₛᵤₚ∸hx≡1⇒x≈0 {x} dₛᵤₚ∸hx≡1 = ≈-resp-h (∸-cancelˡ h≤dₛᵤₚ h≤dₛᵤₚ (begin
      dₛᵤₚ ∸ h x         ≡⟨ dₛᵤₚ∸hx≡1 ⟩
      1                  ≡⟨ cong suc (sym (n∸n≡0 hₘₐₓ)) ⟩
      suc (hₘₐₓ ∸ hₘₐₓ) ≡⟨ sym (+-∸-assoc 1 {hₘₐₓ} ≤ℕ-refl) ⟩
      dₛᵤₚ ∸ hₘₐₓ       ≡⟨ cong (dₛᵤₚ ∸_) hₘₐₓ≡h0 ⟩
      dₛᵤₚ ∸ h 0#       ∎))     
      where open ≡-Reasoning
    
    -- dₕ

    0<dₕ : ∀ {x y} → 0 <ℕ dₕ x y
    0<dₕ = m≤n⇒m≤n⊔o _ 0<dₛᵤₚ∸h

    dₕ<dₘₐₓ : ∀ x y → dₕ x y ≤ℕ dₘₐₓ
    dₕ<dₘₐₓ x y = n≤m×o≤m⇒n⊔o≤m dₛᵤₚ∸h≤dₘₐₓ dₛᵤₚ∸h≤dₘₐₓ
    
    dₕ-sym : ∀ x y → dₕ x y ≡ dₕ y x
    dₕ-sym x y = ⊔-comm (dₛᵤₚ ∸ h x) (dₛᵤₚ ∸ h y)

    dₕ-cong₂ : dₕ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
    dₕ-cong₂ x≈y u≈v = cong₂ (λ x y → (dₛᵤₚ ∸ x) ⊔ (dₛᵤₚ ∸ y))
      (h-resp-≈ x≈y)
      (h-resp-≈ u≈v)

    dₕ-mono-≤ : dₕ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≥ℕ_
    dₕ-mono-≤ x≤y u≤v = ⊔-mono-≤
      (∸-mono ≤ℕ-refl (h-resp-≤ x≤y))
      (∸-mono ≤ℕ-refl (h-resp-≤ u≤v))
    
    dₕ-maxTriIneq : MaxTriangleIneq S dₕ
    dₕ-maxTriIneq x y z = ⊔-mono-≤
      (m≤m⊔n (dₛᵤₚ ∸ h x) (dₛᵤₚ ∸ h y))
      (n≤m⊔n (dₛᵤₚ ∸ h y) (dₛᵤₚ ∸ h z))

    --dₕ≡1⇒x≈0 : ∀ {x y} → dₕ x y ≡ 1 → x ≈ 0#
    --dₕ≡1⇒x≈0 {x} {y} dₕ≡1 = ≈-resp-h (∸-left-cancellative h≤dₛᵤₚ h≤dₛᵤₚ {!!})
    
    postulate dₕ≡1⇒x≈y : ∀ {x y} → dₕ x y ≡ 1 → x ≈ y
    {-
    dₕ≡1⇒x≈y {x} {y} dₕ≡1 with ⊔-sel (dₛᵤₚ ∸ h x) (dₛᵤₚ ∸ h y)
    ... | inj₁ dₕ≡dₛᵤₚ∸hx = trans (dₛᵤₚ∸hx≡1⇒x≈0 (≡-trans (≡-sym dₕ≡dₛᵤₚ∸hx) dₕ≡1)) (sym (dₛᵤₚ∸hx≡1⇒x≈0 {!!}))
    ... | inj₂ dₕ≡dₛᵤₚ∸hy = {!!}
    -}
    
    -- Elementwise distance

    dₑ≤dₘₐₓ : ∀ x y → dₑ x y ≤ℕ dₘₐₓ
    dₑ≤dₘₐₓ x y with x ≟ y
    ... | yes _ = z≤n
    ... | no  _ = dₕ<dₘₐₓ x y

    x≈y⇒dₑ≡0 : ∀ {x y} → x ≈ y → dₑ x y ≡ 0
    x≈y⇒dₑ≡0 {x} {y} x≈y with x ≟ y
    ... | yes _   = refl
    ... | no  x≉y = contradiction x≈y x≉y

    dₑ≡0⇒x≈y : ∀ {x y} → dₑ x y ≡ 0 → x ≈ y
    dₑ≡0⇒x≈y {x} {y} dₑ≡0 with x ≟ y 
    ... | yes x≈y = x≈y
    ... | no  _   = contradiction (sym dₑ≡0) (<⇒≢ 0<dₕ)

    x≉y⇒dₑ≡dₕ : ∀ {x y} → x ≉ y → dₑ x y ≡ dₕ x y
    x≉y⇒dₑ≡dₕ {x} {y} x≉y with x ≟ y
    ... | yes x≈y = contradiction x≈y x≉y
    ... | no  _   = refl

    dₑ≢1 : ∀ x y → dₑ x y ≢ 1
    dₑ≢1 x y dₑ≡1 with x ≟ y
    ... | yes x≈y = contradiction dₑ≡1 λ()
    ... | no  x≉y = contradiction (dₕ≡1⇒x≈y dₑ≡1) x≉y
    
    dₛᵤₚ∸hx≤dₑ : ∀ {x y} → x ≉ y → dₛᵤₚ ∸ h x ≤ℕ dₑ x y
    dₛᵤₚ∸hx≤dₑ {x} {y} x≉y with x ≟ y
    ... | yes x≈y = contradiction x≈y x≉y
    ... | no  _   = m≤m⊔n (dₛᵤₚ ∸ h x) (dₛᵤₚ ∸ h y)

    dₛᵤₚ∸hy≤dₑ : ∀ {x y} → x ≉ y → dₛᵤₚ ∸ h y ≤ℕ dₑ x y
    dₛᵤₚ∸hy≤dₑ {x} {y} x≉y with x ≟ y
    ... | yes x≈y = contradiction x≈y x≉y
    ... | no  _   = n≤m⊔n (dₛᵤₚ ∸ h x) (dₛᵤₚ ∸ h y)
    
    dₑ≡dₛᵤₚ∸hx⇒hx≤hy : ∀ {x y} → dₑ x y ≡ dₛᵤₚ ∸ h x → h x ≤ℕ h y
    dₑ≡dₛᵤₚ∸hx⇒hx≤hy {x} {y} dₑ≡dₘₐₓ∸hx with x ≟ y
    ... | yes x≈y = contradiction (trans dₑ≡dₘₐₓ∸hx (+-∸-assoc 1 h≤hₘₐₓ)) λ()
    ... | no  x≉y = o∸n≤o∸m∧m≤o⇒m≤n (m⊔n≡m⇒n≤m dₑ≡dₘₐₓ∸hx) h≤dₛᵤₚ

    dₑ≡dₛᵤₚ∸hx : ∀ {x y} → h x <ℕ h y → dₑ x y ≡ dₛᵤₚ ∸ h x
    dₑ≡dₛᵤₚ∸hx {x} {y} hx<hy with x ≟ y
    ... | yes x≈y = contradiction (h-resp-≈ x≈y) (<⇒≢ hx<hy)
    ... | no  x≉y = n≤m⇒m⊔n≡m (∸-mono (≤ℕ-refl {dₛᵤₚ}) (<⇒≤ hx<hy))

    dₑ≡dₛᵤₚ∸hy : ∀ {x y} → h y <ℕ h x → dₑ x y ≡ dₛᵤₚ ∸ h y
    dₑ≡dₛᵤₚ∸hy {x} {y} hy<hx with x ≟ y
    ... | yes x≈y = contradiction (h-resp-≈ (≈-sym x≈y)) (<⇒≢ hy<hx)
    ... | no  x≉y = m≤n⇒m⊔n≡n (∸-mono (≤ℕ-refl {dₛᵤₚ}) (<⇒≤ hy<hx))
    
    dₑxy=hx⊎hy : ∀ {x y} → x ≉ y → (dₑ x y ≡ dₛᵤₚ ∸ h x) ⊎ (dₑ x y ≡ dₛᵤₚ ∸ h y)
    dₑxy=hx⊎hy {x} {y} x≉y with x ≟ y
    ... | yes x≈y = contradiction x≈y x≉y
    ... | no  _   = ⊔-sel (dₛᵤₚ ∸ h x) (dₛᵤₚ ∸ h y)

    x≉y⇒0<dₑ : ∀ {x y} → x ≉ y → 0 <ℕ dₑ x y
    x≉y⇒0<dₑ {x} {y} x≉y with x ≟ y
    ... | yes x≈y = contradiction x≈y x≉y
    ... | no  _   = ⊔-mono-≤ 0<dₛᵤₚ∸h 0<dₛᵤₚ∸h
    
    0<dₑ⇒x≉y : ∀ {x y} → 0 <ℕ dₑ x y → x ≉ y
    0<dₑ⇒x≉y {x} {y} 0<dₑ with x ≟ y 
    ... | yes x≈yⱼ = contradiction 0<dₑ 1+n≰n 
    ... | no  x≉y = x≉y

    dₑ-sym : ∀ x y → dₑ x y ≡ dₑ y x
    dₑ-sym x y with x ≟ y | y ≟ x
    ... | yes _   | yes _   = refl
    ... | no  x≉y | yes y≈x = contradiction (≈-sym y≈x) x≉y 
    ... | yes x≈y | no  y≉x = contradiction (≈-sym x≈y) y≉x 
    ... | no  _   | no  _   = dₕ-sym x y

    dₑ-cong₂ : dₑ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
    dₑ-cong₂ {x} {y} {u} {v} x≈y u≈v with x ≟ u | y ≟ v
    ... | yes _   | yes _   = refl
    ... | yes x≈u | no  y≉v = contradiction (≈-trans (≈-trans (≈-sym x≈y) x≈u) u≈v) y≉v
    ... | no  x≉u | yes y≈v = contradiction (≈-trans (≈-trans x≈y y≈v) (≈-sym u≈v)) x≉u
    ... | no  _   | no  _   = dₕ-cong₂ x≈y u≈v

    dₑ-maxTriIneq : MaxTriangleIneq S dₑ
    dₑ-maxTriIneq x y z with x ≟ y | y ≟ z | x ≟ z
    ... | _       | _       | yes _  = z≤n
    ... | yes x≈y | yes y≈z | no x≉z = contradiction (≈-trans x≈y y≈z) x≉z
    ... | yes x≈y | no  _   | no _   = subst (_ ≤ℕ_) (dₕ-cong₂ x≈y ≈-refl) ≤ℕ-refl
    ... | no  _   | no  _   | no _   = dₕ-maxTriIneq x y z
    ... | no  _   | yes y≈z | no _   = begin
      dₕ x z     ≡⟨ dₕ-cong₂ ≈-refl (≈-sym y≈z) ⟩
      dₕ x y     ≡⟨ sym (⊔-identityʳ (dₕ x y)) ⟩
      dₕ x y ⊔ 0 ∎     
      where open ≤-Reasoning
      
    -- dₑ

    d-sym : ∀ X Y → d X Y ≡ d Y X
    d-sym X Y = max⁺-cong (zipWith-sym _≡_ dₑ-sym X Y)

    d-cong₂ : d Preserves₂ _≈ₘ_ ⟶ _≈ₘ_ ⟶ _≡_
    d-cong₂ X≈Y U≈V = max⁺-cong (zipWith-cong _≈_ _≈_ _≡_ dₑ-cong₂ X≈Y U≈V)

    dₑ≤d : ∀ X Y i j → dₑ (X i j) (Y i j) ≤ℕ d X Y
    dₑ≤d X Y i j = M≤max⁺[M] (zipWith dₑ X Y) i j

    d≤dₘₐₓ : ∀ X Y → d X Y ≤ℕ dₘₐₓ
    d≤dₘₐₓ X Y = max⁺[M]≤x (λ i j → dₑ≤dₘₐₓ (X i j) (Y i j))

    d<dₛᵤₚ : ∀ X Y → d X Y <ℕ dₛᵤₚ
    d<dₛᵤₚ X Y = s≤s (d≤dₘₐₓ X Y)
    
    d≤dₛᵤₚ : ∀ X Y → d X Y ≤ℕ dₛᵤₚ
    d≤dₛᵤₚ X Y = <⇒≤ (d<dₛᵤₚ X Y)
    
    dₛᵤₚ∸hXᵢⱼ≤d : ∀ {X Y i j} → X i j ≉ Y i j → dₛᵤₚ ∸ h (X i j) ≤ℕ d X Y
    dₛᵤₚ∸hXᵢⱼ≤d Xᵢⱼ≉Yᵢⱼ = ≤ℕ-trans (dₛᵤₚ∸hx≤dₑ Xᵢⱼ≉Yᵢⱼ) (dₑ≤d _ _ _ _)

    dₛᵤₚ∸hYᵢⱼ≤d : ∀ {X Y i j} → X i j ≉ Y i j → dₛᵤₚ ∸ h (Y i j) ≤ℕ d X Y
    dₛᵤₚ∸hYᵢⱼ≤d Xᵢⱼ≉Yᵢⱼ = ≤ℕ-trans (dₛᵤₚ∸hy≤dₑ Xᵢⱼ≉Yᵢⱼ) (dₑ≤d _ _ _ _)
    
    X≈Y⇒d≡0 : ∀ {X Y} → X ≈ₘ Y → d X Y ≡ 0
    X≈Y⇒d≡0 X≈Y = max⁺-constant (λ i j → x≈y⇒dₑ≡0 (X≈Y i j))
    
    d≡0⇒X≈Y : ∀ {X Y} → d X Y ≡ 0 → X ≈ₘ Y
    d≡0⇒X≈Y {X} {Y} d≡0 i j = dₑ≡0⇒x≈y (≤ℕ-antisym (subst (dₑ (X i j) (Y i j) ≤ℕ_) d≡0 (dₑ≤d X Y i j)) z≤n)

    d≡dₑ : ∀ X Y → ∃₂ λ i j → d X Y ≡ dₑ (X i j) (Y i j)
    d≡dₑ X Y = max⁺[M]∈M (zipWith dₑ X Y)

    d≢1 : ∀ X Y → d X Y ≢ 1
    d≢1 X Y with d≡dₑ X Y
    ... | i , j , d≡dₑ = dₑ≢1 (X i j) (Y i j) ∘ trans (sym d≡dₑ)
    
    d≡dₛᵤₚ∸Xᵢⱼ : ∀ {X Y i j} →
                 (∀ k l → dₑ (X k l) (Y k l) ≤ℕ dₑ (X i j) (Y i j)) →
                 h (X i j) <ℕ h (Y i j) → d X Y ≡ dₛᵤₚ ∸ h (X i j) 
    d≡dₛᵤₚ∸Xᵢⱼ ≤dₑᵢⱼ hXᵢⱼ<hYᵢⱼ = trans (max⁺[M]≡x (_ , _ , refl) ≤dₑᵢⱼ) (dₑ≡dₛᵤₚ∸hx hXᵢⱼ<hYᵢⱼ)
    
    d≡dₛᵤₚ∸Yᵢⱼ : ∀ {X Y i j} →
                 (∀ k l → dₑ (X k l) (Y k l) ≤ℕ dₑ (X i j) (Y i j)) →
                 h (Y i j) <ℕ h (X i j) → d X Y ≡ dₛᵤₚ ∸ h (Y i j)
    d≡dₛᵤₚ∸Yᵢⱼ ≤dₑᵢⱼ hYᵢⱼ<hXᵢⱼ = trans (max⁺[M]≡x (_ , _ , refl) ≤dₑᵢⱼ) (dₑ≡dₛᵤₚ∸hy hYᵢⱼ<hXᵢⱼ)

    d-maxTriIneq : MaxTriangleIneq ℝ𝕄ₛ d
    d-maxTriIneq X Y Z with d≡dₑ X Z
    ... | i , j , dˣᶻ≡ij = begin
      d X Z                                   ≡⟨ dˣᶻ≡ij ⟩
      dₑ (X i j) (Z i j)                      ≤⟨ dₑ-maxTriIneq _ _ _ ⟩
      dₑ (X i j) (Y i j) ⊔ dₑ (Y i j) (Z i j) ≤⟨ ⊔-mono-≤ (dₑ≤d X Y i j) (dₑ≤d Y Z i j) ⟩
      d X Y ⊔ d Y Z                           ∎
      where open ≤-Reasoning

    d-findWorstDisagreement : ∀ {X Y} → X ≉ₘ Y 
                              → ∃₂ λ i j 
                                 → X i j ≉ Y i j
                                   × d X Y ≡ dₑ (X i j) (Y i j)
                                   × (dₑ (X i j) (Y i j) ≡ dₛᵤₚ ∸ h (X i j) ⊎ dₑ (X i j) (Y i j) ≡ dₛᵤₚ ∸ h (Y i j))
    d-findWorstDisagreement {X} {Y} X≉Y with d X Y ≟ℕ 0 | d≡dₑ X Y 
    ... | yes d≡0 | _ = contradiction (d≡0⇒X≈Y d≡0) X≉Y
    ... | no  d≢0 | i , j , d≡dₑXᵢⱼYᵢⱼ with λ Xᵢⱼ≈Yᵢⱼ → d≢0 (trans d≡dₑXᵢⱼYᵢⱼ (x≈y⇒dₑ≡0 Xᵢⱼ≈Yᵢⱼ))
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
