open import Data.Fin using (Fin)
open import Data.List using (List)
open import Data.List.Any.Membership.Propositional using (_∈_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Nat using (ℕ; suc; zero; z≤n; s≤s; _⊔_; _*_; _∸_) renaming (_≤_ to _≤ℕ_; _<_ to _<ℕ_)
open import Data.Nat.Properties as ℕₚ using (⊔-mono-≤) renaming (≤-antisym to ≤ℕ-antisym; ≤-decTotalOrder to ≤ℕ-decTotalOrder)
open import Data.Product using (∃; _,_; proj₁; proj₂)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (_Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; module ≡-Reasoning)
import Relation.Binary.PartialOrderReasoning as PO-Reasoning

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
    ; d-strContr
    ; d-mono
    )


  D : RMatrix → RMatrix → ℕ
  D X Y = max⁺ (zipWith d X Y)

  abstract
  
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
      where open ℕₚ.≤-Reasoning


  -- Strictly contracting --

  module PostDisagreementResult 
    {X Y i j} (D≡dᵢⱼ : D (σ X) (σ Y) ≡ d (σ X i j) (σ Y i j))
    (σXᵢⱼ<σYᵢⱼ : σ X i j < σ Y i j) 
    where 

    σXᵢⱼ≤σYᵢⱼ : σ X i j ≤ σ Y i j
    σXᵢⱼ≤σYᵢⱼ = proj₁ σXᵢⱼ<σYᵢⱼ

    σXᵢⱼ≉σYᵢⱼ : σ X i j ≉ σ Y i j
    σXᵢⱼ≉σYᵢⱼ = proj₂ σXᵢⱼ<σYᵢⱼ
    
    i≢j : i ≢ j
    i≢j refl = σXᵢⱼ≉σYᵢⱼ (σXᵢᵢ≈σYᵢᵢ X Y i)

    σXᵢⱼ≉Iᵢⱼ : σ X i j ≉ I i j
    σXᵢⱼ≉Iᵢⱼ σXᵢⱼ≈Iᵢⱼ = σXᵢⱼ≉σYᵢⱼ (≤-antisym σXᵢⱼ≤σYᵢⱼ (begin
      σ Y i j   ≤⟨ 0#-idₗ-⊕ _ ⟩
      0#        ≈⟨ ≈-sym (≈-reflexive (Iᵢⱼ≡0# (i≢j ∘ sym))) ⟩
      I i j     ≈⟨ ≈-sym σXᵢⱼ≈Iᵢⱼ ⟩
      σ X i j   ∎))
      where open PO-Reasoning ≤-poset

    Xₖⱼ≉Yₖⱼ : ∀ {k} → σ X i j ≈ A i k ▷ X k j → X k j ≉ Y k j
    Xₖⱼ≉Yₖⱼ {k} σXᵢⱼ≈Aᵢₖ▷Xₖⱼ Xₖⱼ≈Yₖⱼ = σXᵢⱼ≉σYᵢⱼ ( ≤-antisym σXᵢⱼ≤σYᵢⱼ (begin
      σ Y i j       ≤⟨ σXᵢⱼ≤Aᵢₖ▷Xₖⱼ Y i j k ⟩
      A i k ▷ Y k j ≈⟨ ▷-cong (A i k) (≈-sym Xₖⱼ≈Yₖⱼ) ⟩
      A i k ▷ X k j ≈⟨ ≈-sym σXᵢⱼ≈Aᵢₖ▷Xₖⱼ ⟩
      σ X i j       ∎))
      where open PO-Reasoning ≤-poset

    σXᵢⱼ≤Aᵢₖ▷Yₖⱼ : ∀ k → σ X i j ≤ A i k ▷ Y k j
    σXᵢⱼ≤Aᵢₖ▷Yₖⱼ k = ≤-trans σXᵢⱼ≤σYᵢⱼ (σXᵢⱼ≤Aᵢₖ▷Xₖⱼ Y i j k)
    
    σXᵢⱼ≉Aᵢₖ▷Yₖⱼ : ∀ k → σ X i j ≉ A i k ▷ Y k j
    σXᵢⱼ≉Aᵢₖ▷Yₖⱼ k σXᵢⱼ≈AᵢₖYₖⱼ = σXᵢⱼ≉σYᵢⱼ (≤-antisym σXᵢⱼ≤σYᵢⱼ (≤-trans (σXᵢⱼ≤Aᵢₖ▷Xₖⱼ Y i j k) (≤-reflexive (≈-sym σXᵢⱼ≈AᵢₖYₖⱼ))))


    result : D (σ X) (σ Y) <ℕ D X Y
    result with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ X i j
    ... | inj₂ σXᵢⱼ≈Iᵢⱼ           = contradiction σXᵢⱼ≈Iᵢⱼ σXᵢⱼ≉Iᵢⱼ
    ... | inj₁ (k , σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) = begin
      suc (D (σ X) (σ Y))                     ≡⟨ cong suc D≡dᵢⱼ ⟩ 
      suc (d (σ X i j) (σ Y i j))             ≤⟨ s≤s (d-mono σXᵢⱼ≤σYᵢⱼ (σXᵢⱼ≤Aᵢₖ▷Yₖⱼ k , σXᵢⱼ≉Aᵢₖ▷Yₖⱼ k)) ⟩
      suc (d (σ X i j) (A i k ▷ Y k j))       ≡⟨ cong suc (d-cong σXᵢⱼ≈Aᵢₖ▷Xₖⱼ ≈-refl) ⟩
      suc (d (A i k ▷ X k j) (A i k ▷ Y k j)) ≤⟨ d-strContr (A i k) (Xₖⱼ≉Yₖⱼ σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) ⟩
      d (X k j) (Y k j)                       ≤⟨ M≤max⁺[M] _ k j ⟩
      D X Y                                   ∎
      where open ℕₚ.≤-Reasoning


{-

  abstract

    open PostDisagreementResult using (result)
    open import RoutingLib.Function.Distance ℝ𝕄ₛ using (_StrContrOver_; _StrContrOnOrbitsOver_)
    open import RoutingLib.Function.Distance.Properties using (strContr⇒strContrOnOrbits)

    σ-strictlyContracting : σ StrContrOver D
    σ-strictlyContracting {X} {Y} Y≉X with σ X ≟ₘ σ Y | D X Y ≟ℕ 0
    ... | yes σX≈σY | yes D≡0 = contradiction (D≡0⇒X≈Y D≡0) (Y≉X ∘ ≈ₘ-sym)
    ... | yes σX≈σY | no  D≢0 rewrite X≈Y⇒D≡0 σX≈σY = n≢0⇒0<n D≢0
    ... | no  σX≉σY | _       with D-findWorstDisagreement σX≉σY
    ...   | i , j , σXᵢⱼ≉σYᵢⱼ , D≡dᵢⱼ , inj₁ dᵢⱼ≡dₛᵤₚ∸hσXᵢⱼ = result σXᵢⱼ≉σYᵢⱼ D≡dᵢⱼ dᵢⱼ≡dₛᵤₚ∸hσXᵢⱼ 
    ...   | i , j , σXᵢⱼ≉σYᵢⱼ , D≡dᵢⱼ , inj₂ dᵢⱼ≡dₛᵤₚ∸hσYᵢⱼ = 
      subst₂ _<ℕ_ (D-sym (σ Y) (σ X)) (D-sym Y X) (
        result 
          (σXᵢⱼ≉σYᵢⱼ ∘ ≈-sym) 
          (trans (trans (D-sym (σ Y) (σ X)) D≡dᵢⱼ) (d-sym (σ X i j) (σ Y i j))) 
          (trans (d-sym (σ Y i j) (σ X i j)) dᵢⱼ≡dₛᵤₚ∸hσYᵢⱼ))

    σ-strictlyContractingOnOrbits : σ StrContrOnOrbitsOver D
    σ-strictlyContractingOnOrbits = strContr⇒strContrOnOrbits ℝ𝕄ₛ σ-strictlyContracting
-}




{-
    
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
