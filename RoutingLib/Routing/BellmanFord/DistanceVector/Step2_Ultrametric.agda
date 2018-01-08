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
open import RoutingLib.Routing.BellmanFord.DistanceVector.SufficientConditions
import RoutingLib.Routing.BellmanFord.DistanceVector.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.DistanceVector.Step1_HeightFunction as Step1

module RoutingLib.Routing.BellmanFord.DistanceVector.Step2_Ultrametric
  {a b ℓ n-1}
  {𝓡𝓐 : RoutingAlgebra a b ℓ}
  (𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1)) 
  (𝓢𝓒 : SufficientConditions 𝓡𝓐)
  where
  
  open Prelude 𝓡𝓟 𝓢𝓒
  open Step1 𝓡𝓟 𝓢𝓒

  -- maximum distance value
  Dₘₐₓ : ℕ
  Dₘₐₓ = hₘₐₓ

  Dₛᵤₚ : ℕ
  Dₛᵤₚ = suc Dₘₐₓ

  abstract

    1≤Dₘₐₓ : 1 ≤ℕ Dₘₐₓ
    1≤Dₘₐₓ = 1≤hₘₐₓ
    
    h≤Dₛᵤₚ : ∀ {x} → h x ≤ℕ Dₛᵤₚ
    h≤Dₛᵤₚ = ≤ℕ-trans h≤hₘₐₓ (n≤1+n hₘₐₓ)

    0<Dₛᵤₚ∸h : ∀ {x} → 0 <ℕ Dₛᵤₚ ∸ h x
    0<Dₛᵤₚ∸h = m<n⇒0<n∸m (s≤s h≤hₘₐₓ)

    Dₛᵤₚ∸h≤dₘₐₓ : ∀ {x} → (suc Dₘₐₓ) ∸ h x ≤ℕ Dₘₐₓ
    Dₛᵤₚ∸h≤dₘₐₓ {x} with m<n⇒n≡1+o (1≤h x)
    ... | (o , h≡1+o) rewrite h≡1+o = n∸m≤n o hₘₐₓ

    Dₛᵤₚ∸hx≡1⇒x≈0 : ∀ {x} → Dₛᵤₚ ∸ h x ≡ 1 → x ≈ 0#
    Dₛᵤₚ∸hx≡1⇒x≈0 {x} Dₛᵤₚ∸hx≡1 = ≈-resp-h (∸-cancelˡ h≤Dₛᵤₚ h≤Dₛᵤₚ (begin
      Dₛᵤₚ ∸ h x         ≡⟨ Dₛᵤₚ∸hx≡1 ⟩
      1                  ≡⟨ cong suc (sym (n∸n≡0 hₘₐₓ)) ⟩
      suc (hₘₐₓ ∸ hₘₐₓ) ≡⟨ sym (+-∸-assoc 1 {hₘₐₓ} ≤ℕ-refl) ⟩
      Dₛᵤₚ ∸ hₘₐₓ       ≡⟨ cong (Dₛᵤₚ ∸_) hₘₐₓ≡h0 ⟩
      Dₛᵤₚ ∸ h 0#       ∎))     
      where open ≡-Reasoning
      
    ----------------------------------------
    -- Invert
    -- an intermediate helper function
    
    invert : Route → Route → ℕ
    invert x y = (Dₛᵤₚ ∸ h x) ⊔ (Dₛᵤₚ ∸ h y)

    0<invert : ∀ {x y} → 0 <ℕ invert x y
    0<invert = m≤n⇒m≤n⊔o _ 0<Dₛᵤₚ∸h

    invert<dₘₐₓ : ∀ x y → invert x y ≤ℕ Dₘₐₓ
    invert<dₘₐₓ x y = n≤m×o≤m⇒n⊔o≤m Dₛᵤₚ∸h≤dₘₐₓ Dₛᵤₚ∸h≤dₘₐₓ
    
    invert-sym : ∀ x y → invert x y ≡ invert y x
    invert-sym x y = ⊔-comm (Dₛᵤₚ ∸ h x) (Dₛᵤₚ ∸ h y)

    invert-cong₂ : invert Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
    invert-cong₂ x≈y u≈v = cong₂ (λ x y → (Dₛᵤₚ ∸ x) ⊔ (Dₛᵤₚ ∸ y))
      (h-resp-≈ x≈y)
      (h-resp-≈ u≈v)

    invert-mono-≤ : invert Preserves₂ _≤_ ⟶ _≤_ ⟶ _≥ℕ_
    invert-mono-≤ x≤y u≤v = ⊔-mono-≤
      (∸-mono ≤ℕ-refl (h-resp-≤ x≤y))
      (∸-mono ≤ℕ-refl (h-resp-≤ u≤v))
    
    invert-maxTriIneq : MaxTriangleIneq S invert
    invert-maxTriIneq x y z = ⊔-mono-≤
      (m≤m⊔n (Dₛᵤₚ ∸ h x) (Dₛᵤₚ ∸ h y))
      (n≤m⊔n (Dₛᵤₚ ∸ h y) (Dₛᵤₚ ∸ h z))

    --invert≡1⇒x≈0 : ∀ {x y} → invert x y ≡ 1 → x ≈ 0#
    --invert≡1⇒x≈0 {x} {y} invert≡1 = ≈-resp-h (∸-left-cancellative h≤Dₛᵤₚ h≤Dₛᵤₚ {!!})
    
    postulate invert≡1⇒x≈y : ∀ {x y} → invert x y ≡ 1 → x ≈ y
    {-
    invert≡1⇒x≈y {x} {y} invert≡1 with ⊔-sel (Dₛᵤₚ ∸ h x) (Dₛᵤₚ ∸ h y)
    ... | inj₁ invert≡Dₛᵤₚ∸hx = trans (Dₛᵤₚ∸hx≡1⇒x≈0 (≡-trans (≡-sym invert≡Dₛᵤₚ∸hx) invert≡1)) (sym (Dₛᵤₚ∸hx≡1⇒x≈0 {!!}))
    ... | inj₂ invert≡Dₛᵤₚ∸hy = {!!}
    -}

    ----------------------------
    -- distance between two routes
    
    d : Route → Route → ℕ
    d x y with x ≟ y
    ... | yes _ = zero
    ... | no  _ = invert x y

    d≤dₘₐₓ : ∀ x y → d x y ≤ℕ Dₘₐₓ
    d≤dₘₐₓ x y with x ≟ y
    ... | yes _ = z≤n
    ... | no  _ = invert<dₘₐₓ x y

    x≈y⇒d≡0 : ∀ {x y} → x ≈ y → d x y ≡ 0
    x≈y⇒d≡0 {x} {y} x≈y with x ≟ y
    ... | yes _   = refl
    ... | no  x≉y = contradiction x≈y x≉y

    d≡0⇒x≈y : ∀ {x y} → d x y ≡ 0 → x ≈ y
    d≡0⇒x≈y {x} {y} d≡0 with x ≟ y 
    ... | yes x≈y = x≈y
    ... | no  _   = contradiction (sym d≡0) (<⇒≢ 0<invert)

    x≉y⇒d≡invert : ∀ {x y} → x ≉ y → d x y ≡ invert x y
    x≉y⇒d≡invert {x} {y} x≉y with x ≟ y
    ... | yes x≈y = contradiction x≈y x≉y
    ... | no  _   = refl

    d≢1 : ∀ x y → d x y ≢ 1
    d≢1 x y d≡1 with x ≟ y
    ... | yes x≈y = contradiction d≡1 λ()
    ... | no  x≉y = contradiction (invert≡1⇒x≈y d≡1) x≉y
    
    Dₛᵤₚ∸hx≤d : ∀ {x y} → x ≉ y → Dₛᵤₚ ∸ h x ≤ℕ d x y
    Dₛᵤₚ∸hx≤d {x} {y} x≉y with x ≟ y
    ... | yes x≈y = contradiction x≈y x≉y
    ... | no  _   = m≤m⊔n (Dₛᵤₚ ∸ h x) (Dₛᵤₚ ∸ h y)

    Dₛᵤₚ∸hy≤d : ∀ {x y} → x ≉ y → Dₛᵤₚ ∸ h y ≤ℕ d x y
    Dₛᵤₚ∸hy≤d {x} {y} x≉y with x ≟ y
    ... | yes x≈y = contradiction x≈y x≉y
    ... | no  _   = n≤m⊔n (Dₛᵤₚ ∸ h x) (Dₛᵤₚ ∸ h y)
    
    d≡Dₛᵤₚ∸hx⇒hx≤hy : ∀ {x y} → d x y ≡ Dₛᵤₚ ∸ h x → h x ≤ℕ h y
    d≡Dₛᵤₚ∸hx⇒hx≤hy {x} {y} d≡dₘₐₓ∸hx with x ≟ y
    ... | yes x≈y = contradiction (trans d≡dₘₐₓ∸hx (+-∸-assoc 1 h≤hₘₐₓ)) λ()
    ... | no  x≉y = o∸n≤o∸m∧m≤o⇒m≤n (m⊔n≡m⇒n≤m d≡dₘₐₓ∸hx) h≤Dₛᵤₚ

    d≡Dₛᵤₚ∸hx : ∀ {x y} → h x <ℕ h y → d x y ≡ Dₛᵤₚ ∸ h x
    d≡Dₛᵤₚ∸hx {x} {y} hx<hy with x ≟ y
    ... | yes x≈y = contradiction (h-resp-≈ x≈y) (<⇒≢ hx<hy)
    ... | no  x≉y = n≤m⇒m⊔n≡m (∸-mono (≤ℕ-refl {Dₛᵤₚ}) (<⇒≤ hx<hy))

    d≡Dₛᵤₚ∸hy : ∀ {x y} → h y <ℕ h x → d x y ≡ Dₛᵤₚ ∸ h y
    d≡Dₛᵤₚ∸hy {x} {y} hy<hx with x ≟ y
    ... | yes x≈y = contradiction (h-resp-≈ (≈-sym x≈y)) (<⇒≢ hy<hx)
    ... | no  x≉y = m≤n⇒m⊔n≡n (∸-mono (≤ℕ-refl {Dₛᵤₚ}) (<⇒≤ hy<hx))
    
    dxy=hx⊎hy : ∀ {x y} → x ≉ y → (d x y ≡ Dₛᵤₚ ∸ h x) ⊎ (d x y ≡ Dₛᵤₚ ∸ h y)
    dxy=hx⊎hy {x} {y} x≉y with x ≟ y
    ... | yes x≈y = contradiction x≈y x≉y
    ... | no  _   = ⊔-sel (Dₛᵤₚ ∸ h x) (Dₛᵤₚ ∸ h y)

    x≉y⇒0<d : ∀ {x y} → x ≉ y → 0 <ℕ d x y
    x≉y⇒0<d {x} {y} x≉y with x ≟ y
    ... | yes x≈y = contradiction x≈y x≉y
    ... | no  _   = ⊔-mono-≤ 0<Dₛᵤₚ∸h 0<Dₛᵤₚ∸h
    
    0<d⇒x≉y : ∀ {x y} → 0 <ℕ d x y → x ≉ y
    0<d⇒x≉y {x} {y} 0<d with x ≟ y 
    ... | yes x≈yⱼ = contradiction 0<d 1+n≰n 
    ... | no  x≉y = x≉y

    d-sym : ∀ x y → d x y ≡ d y x
    d-sym x y with x ≟ y | y ≟ x
    ... | yes _   | yes _   = refl
    ... | no  x≉y | yes y≈x = contradiction (≈-sym y≈x) x≉y 
    ... | yes x≈y | no  y≉x = contradiction (≈-sym x≈y) y≉x 
    ... | no  _   | no  _   = invert-sym x y

    d-cong₂ : d Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
    d-cong₂ {x} {y} {u} {v} x≈y u≈v with x ≟ u | y ≟ v
    ... | yes _   | yes _   = refl
    ... | yes x≈u | no  y≉v = contradiction (≈-trans (≈-trans (≈-sym x≈y) x≈u) u≈v) y≉v
    ... | no  x≉u | yes y≈v = contradiction (≈-trans (≈-trans x≈y y≈v) (≈-sym u≈v)) x≉u
    ... | no  _   | no  _   = invert-cong₂ x≈y u≈v

    d-maxTriIneq : MaxTriangleIneq S d
    d-maxTriIneq x y z with x ≟ y | y ≟ z | x ≟ z
    ... | _       | _       | yes _  = z≤n
    ... | yes x≈y | yes y≈z | no x≉z = contradiction (≈-trans x≈y y≈z) x≉z
    ... | yes x≈y | no  _   | no _   = subst (_ ≤ℕ_) (invert-cong₂ x≈y ≈-refl) ≤ℕ-refl
    ... | no  _   | no  _   | no _   = invert-maxTriIneq x y z
    ... | no  _   | yes y≈z | no _   = begin
      invert x z     ≡⟨ invert-cong₂ ≈-refl (≈-sym y≈z) ⟩
      invert x y     ≡⟨ sym (⊔-identityʳ (invert x y)) ⟩
      invert x y ⊔ 0 ∎     
      where open ≤-Reasoning
      
    -----------------
    -- the overall distance between two routing states

  abstract
  
    D : RMatrix → RMatrix → ℕ
    D X Y = max⁺ (zipWith d X Y)

    D-sym : ∀ X Y → D X Y ≡ D Y X
    D-sym X Y = max⁺-cong (zipWith-sym _≡_ d-sym X Y)

    D-cong₂ : D Preserves₂ _≈ₘ_ ⟶ _≈ₘ_ ⟶ _≡_
    D-cong₂ X≈Y U≈V = max⁺-cong (zipWith-cong _≈_ _≈_ _≡_ d-cong₂ X≈Y U≈V)

    d≤D : ∀ X Y i j → d (X i j) (Y i j) ≤ℕ D X Y
    d≤D X Y i j = M≤max⁺[M] (zipWith d X Y) i j

    D≤dₘₐₓ : ∀ X Y → D X Y ≤ℕ Dₘₐₓ
    D≤dₘₐₓ X Y = max⁺[M]≤x (λ i j → d≤dₘₐₓ (X i j) (Y i j))

    D<Dₛᵤₚ : ∀ X Y → D X Y <ℕ Dₛᵤₚ
    D<Dₛᵤₚ X Y = s≤s (D≤dₘₐₓ X Y)
    
    D≤Dₛᵤₚ : ∀ X Y → D X Y ≤ℕ Dₛᵤₚ
    D≤Dₛᵤₚ X Y = <⇒≤ (D<Dₛᵤₚ X Y)
    
    Dₛᵤₚ∸hXᵢⱼ≤D : ∀ {X Y i j} → X i j ≉ Y i j → Dₛᵤₚ ∸ h (X i j) ≤ℕ D X Y
    Dₛᵤₚ∸hXᵢⱼ≤D Xᵢⱼ≉Yᵢⱼ = ≤ℕ-trans (Dₛᵤₚ∸hx≤d Xᵢⱼ≉Yᵢⱼ) (d≤D _ _ _ _)

    Dₛᵤₚ∸hYᵢⱼ≤D : ∀ {X Y i j} → X i j ≉ Y i j → Dₛᵤₚ ∸ h (Y i j) ≤ℕ D X Y
    Dₛᵤₚ∸hYᵢⱼ≤D Xᵢⱼ≉Yᵢⱼ = ≤ℕ-trans (Dₛᵤₚ∸hy≤d Xᵢⱼ≉Yᵢⱼ) (d≤D _ _ _ _)
    
    X≈Y⇒D≡0 : ∀ {X Y} → X ≈ₘ Y → D X Y ≡ 0
    X≈Y⇒D≡0 X≈Y = max⁺-constant (λ i j → x≈y⇒d≡0 (X≈Y i j))
    
    D≡0⇒X≈Y : ∀ {X Y} → D X Y ≡ 0 → X ≈ₘ Y
    D≡0⇒X≈Y {X} {Y} d≡0 i j = d≡0⇒x≈y (≤ℕ-antisym (subst (d (X i j) (Y i j) ≤ℕ_) d≡0 (d≤D X Y i j)) z≤n)

    D≡d : ∀ X Y → ∃₂ λ i j → D X Y ≡ d (X i j) (Y i j)
    D≡d X Y = max⁺[M]∈M (zipWith d X Y)

    D≢1 : ∀ X Y → D X Y ≢ 1
    D≢1 X Y with D≡d X Y
    ... | i , j , D≡d = d≢1 (X i j) (Y i j) ∘ trans (sym D≡d)
    
    D≡Dₛᵤₚ∸Xᵢⱼ : ∀ {X Y i j} →
                 (∀ k l → d (X k l) (Y k l) ≤ℕ d (X i j) (Y i j)) →
                 h (X i j) <ℕ h (Y i j) → D X Y ≡ Dₛᵤₚ ∸ h (X i j) 
    D≡Dₛᵤₚ∸Xᵢⱼ ≤dₑᵢⱼ hXᵢⱼ<hYᵢⱼ = trans (max⁺[M]≡x (_ , _ , refl) ≤dₑᵢⱼ) (d≡Dₛᵤₚ∸hx hXᵢⱼ<hYᵢⱼ)
    
    D≡Dₛᵤₚ∸Yᵢⱼ : ∀ {X Y i j} →
                 (∀ k l → d (X k l) (Y k l) ≤ℕ d (X i j) (Y i j)) →
                 h (Y i j) <ℕ h (X i j) → D X Y ≡ Dₛᵤₚ ∸ h (Y i j)
    D≡Dₛᵤₚ∸Yᵢⱼ ≤dₑᵢⱼ hYᵢⱼ<hXᵢⱼ = trans (max⁺[M]≡x (_ , _ , refl) ≤dₑᵢⱼ) (d≡Dₛᵤₚ∸hy hYᵢⱼ<hXᵢⱼ)

    D-maxTriIneq : MaxTriangleIneq ℝ𝕄ₛ D
    D-maxTriIneq X Y Z with D≡d X Z
    ... | i , j , dˣᶻ≡ij = begin
      D X Z                                 ≡⟨ dˣᶻ≡ij ⟩
      d (X i j) (Z i j)                     ≤⟨ d-maxTriIneq _ _ _ ⟩
      d (X i j) (Y i j) ⊔ d (Y i j) (Z i j) ≤⟨ ⊔-mono-≤ (d≤D X Y i j) (d≤D Y Z i j) ⟩
      D X Y ⊔ D Y Z                         ∎
      where open ≤-Reasoning

    D-findWorstDisagreement : ∀ {X Y} → X ≉ₘ Y 
                              → ∃₂ λ i j 
                                 → X i j ≉ Y i j
                                   × D X Y ≡ d (X i j) (Y i j)
                                   × (d (X i j) (Y i j) ≡ Dₛᵤₚ ∸ h (X i j) ⊎ d (X i j) (Y i j) ≡ Dₛᵤₚ ∸ h (Y i j))
    D-findWorstDisagreement {X} {Y} X≉Y with D X Y ≟ℕ 0 | D≡d X Y 
    ... | yes D≡0 | _ = contradiction (D≡0⇒X≈Y D≡0) X≉Y
    ... | no  D≢0 | i , j , D≡dXᵢⱼYᵢⱼ with λ Xᵢⱼ≈Yᵢⱼ → D≢0 (trans D≡dXᵢⱼYᵢⱼ (x≈y⇒d≡0 Xᵢⱼ≈Yᵢⱼ))
    ...   | Xᵢⱼ≉Yᵢⱼ  = i , j , Xᵢⱼ≉Yᵢⱼ , D≡dXᵢⱼYᵢⱼ , dxy=hx⊎hy Xᵢⱼ≉Yᵢⱼ
    
    -----------------
    -- Ultrametric --
    -----------------
    -- We have now shown that d is an ultrametric

    D-isUltrametric : IsUltrametric ℝ𝕄ₛ D
    D-isUltrametric = record 
      { eq⇒0        = X≈Y⇒D≡0 
      ; 0⇒eq        = D≡0⇒X≈Y 
      ; sym         = D-sym 
      ; maxTriangle = D-maxTriIneq 
      }
