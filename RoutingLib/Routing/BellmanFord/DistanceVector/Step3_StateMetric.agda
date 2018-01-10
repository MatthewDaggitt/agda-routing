open import Data.Fin using (Fin)
open import Data.List using (List)
open import Data.List.Any.Membership.Propositional using (_∈_)
open import Data.Nat using (ℕ; suc; zero; z≤n; s≤s; _⊔_; _*_; _∸_) renaming (_≤_ to _≤ℕ_; _<_ to _<ℕ_)
open import Data.Nat.Properties using (⊔-mono-≤; module ≤-Reasoning) renaming (≤-antisym to ≤ℕ-antisym; ≤-decTotalOrder to ≤ℕ-decTotalOrder)
open import Data.Product using (∃; _,_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (_Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; module ≡-Reasoning)

open import RoutingLib.Data.List using (between)
open import RoutingLib.Data.List.Uniqueness.Propositional using (Unique)
open import RoutingLib.Data.List.Sorting using (Sorted)
open import RoutingLib.Data.Nat.Properties using (ℕₛ)
open import RoutingLib.Function.Distance using (IsUltrametric; MaxTriangleIneq)
open import RoutingLib.Data.Matrix using (Matrix; zipWith; max⁺)
open import RoutingLib.Data.Matrix.Properties using (max⁺-cong; M≤max⁺[M]; max⁺[M]≡x; max⁺[M]≤x; max⁺-constant; zipWith-sym)
open import RoutingLib.Data.Matrix.Membership.Propositional.Properties using (max⁺[M]∈M)
open import RoutingLib.Data.Matrix.Relation.Pointwise using (zipWith-cong)

open import RoutingLib.Routing.Definitions using (RoutingProblem; RoutingAlgebra)
open import RoutingLib.Routing.BellmanFord.DistanceVector.SufficientConditions
import RoutingLib.Routing.BellmanFord.DistanceVector.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.DistanceVector.Step2_RouteMetric as Step2

module RoutingLib.Routing.BellmanFord.DistanceVector.Step3_StateMetric
  {a b ℓ n-1}
  {𝓡𝓐 : RoutingAlgebra a b ℓ}
  (𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1)) 
  (𝓢𝓒 : SufficientConditions 𝓡𝓐)
  where
  
  open Prelude 𝓡𝓟 𝓢𝓒
  open Step2 𝓡𝓟 𝓢𝓒 using
    ( d
    ; d-cong
    ; x≈y⇒d≡0
    ; d≡0⇒x≈y
    ; d-sym
    ; d-maxTriIneq
    ; d-image
    ; d-image!
    ; d-image-sound
    ; d-image-complete
    ; d-image↗
    )



  abstract
  
    D : RMatrix → RMatrix → ℕ
    D X Y = max⁺ (zipWith d X Y)

    D-cong : D Preserves₂ _≈ₘ_ ⟶ _≈ₘ_ ⟶ _≡_
    D-cong X≈Y U≈V = max⁺-cong (zipWith-cong _≈_ _≈_ _≡_ d-cong X≈Y U≈V)
    
    d≤D : ∀ X Y i j → d (X i j) (Y i j) ≤ℕ D X Y
    d≤D X Y i j = M≤max⁺[M] (zipWith d X Y) i j
    
    D-sym : ∀ X Y → D X Y ≡ D Y X
    D-sym X Y = max⁺-cong (zipWith-sym _≡_ d-sym X Y)

    X≈Y⇒D≡0 : ∀ {X Y} → X ≈ₘ Y → D X Y ≡ 0
    X≈Y⇒D≡0 X≈Y = max⁺-constant (λ i j → x≈y⇒d≡0 (X≈Y i j))
    
    D≡0⇒X≈Y : ∀ {X Y} → D X Y ≡ 0 → X ≈ₘ Y
    D≡0⇒X≈Y {X} {Y} d≡0 i j = d≡0⇒x≈y (≤ℕ-antisym (subst (d (X i j) (Y i j) ≤ℕ_) d≡0 (d≤D X Y i j)) z≤n)

    D-maxTriIneq : MaxTriangleIneq ℝ𝕄ₛ D
    D-maxTriIneq X Y Z with max⁺[M]∈M (zipWith d X Z)
    ... | i , j , dˣᶻ≡ij = begin
      D X Z                                 ≡⟨ dˣᶻ≡ij ⟩
      d (X i j) (Z i j)                     ≤⟨ d-maxTriIneq _ _ _ ⟩
      d (X i j) (Y i j) ⊔ d (Y i j) (Z i j) ≤⟨ ⊔-mono-≤ (d≤D X Y i j) (d≤D Y Z i j) ⟩
      D X Y ⊔ D Y Z                         ∎
      where open ≤-Reasoning


    -- We can therefore reconstruct the image of d X for any X

    module _ (X : RMatrix) where

      -- Find the maximal entries of X
      s : Fin n
      s with maxRoute[X]∈X X
      ... | s , _ , _ = s
  
      t : Fin n
      t with maxRoute[X]∈X X
      ... | _ , t , _ = t

      Xᵢⱼ≤Xₛₜ : ∀ i j → X s t ≤ X i j 
      Xᵢⱼ≤Xₛₜ i j with maxRoute[X]∈X X
      ... | s , t , max⁺≈Xₛₜ = ≤-trans (≤-reflexive (≈-sym max⁺≈Xₛₜ)) (maxRoute[X]<X X i j) 

      

      D-image : List ℕ
      D-image = {!between ? ?!}
    
      D-image! : Unique D-image
      D-image! = {!!}
  
      D-image-complete : ∀ Y → D X Y ∈ D-image
      D-image-complete Y = {!!}

      D-image-sound : ∀ {i} → i ∈ D-image → ∃ λ Y → D X Y ≡ i
      D-image-sound {i} i∈betw = {!!}

      D-image↗ : Sorted ≤ℕ-decTotalOrder D-image
      D-image↗ = {!!}







{-
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
-}
