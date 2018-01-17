open import Data.Fin using (Fin; zero)
open import Data.List using (List)
open import Data.List.Any.Membership.Propositional using (_∈_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Nat using (ℕ; suc; zero; z≤n; s≤s; _⊔_; _*_; _∸_) renaming (_≤_ to _≤ℕ_; _<_ to _<ℕ_)
open import Data.Nat.Properties as ℕₚ using (⊔-mono-≤) renaming (≤-trans to ≤ℕ-trans; ≤-antisym to ≤ℕ-antisym; ≤-decTotalOrder to ≤ℕ-decTotalOrder)
open import Data.Product using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Data.List using (upTo)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (_Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; module ≡-Reasoning)
import Relation.Binary.PartialOrderReasoning as PO-Reasoning

open import RoutingLib.Data.List using (between)
open import RoutingLib.Data.List.Uniqueness.Propositional using (Unique)
open import RoutingLib.Data.List.Membership.Propositional.Properties using (∈-upTo⁺)
open import RoutingLib.Data.List.Sorting using (Sorted)
open import RoutingLib.Data.Table using (Table; max⁺; zipWith)
open import RoutingLib.Data.Nat.Properties as Rℕₚ using (ℕₛ; n≢0⇒0<n)
open import RoutingLib.Function.Distance using (IsUltrametric; MaxTriangleIneq)
open import RoutingLib.Data.Matrix using (Matrix)
open import RoutingLib.Data.Matrix.Properties using (max⁺-cong; M≤max⁺[M]; max⁺[M]≡x; max⁺[M]≤x; max⁺-constant; zipWith-sym)
open import RoutingLib.Data.Matrix.Membership.Propositional.Properties using (max⁺[M]∈M)
open import RoutingLib.Data.Matrix.Relation.Pointwise using (zipWith-cong)

open import RoutingLib.Routing.Definitions using (RoutingProblem; RoutingAlgebra)
open import RoutingLib.Routing.BellmanFord.DistanceVector.SufficientConditions
open import RoutingLib.Function.Distance using (Ultrametric)
import RoutingLib.Routing.BellmanFord.DistanceVector.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.DistanceVector.Step2_RouteMetric as Step2
import RoutingLib.Function.Distance.MaxLift as MaxLift
open import RoutingLib.Function.Image using (FiniteImage)

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
    ; d≤H
    ; d-ultrametric
    )


  -------------------------------------
  -- Ultrametric over routing tables --
  -------------------------------------

  dᵢ-ultrametric : Ultrametric _
  dᵢ-ultrametric = MaxLift.ultrametric {n = n} (λ _ → S) (λ _ → d-ultrametric)

  open Ultrametric dᵢ-ultrametric public using ()
    renaming
    ( d to dᵢ
    ; isUltrametric to dᵢ-isUltrametric
    )

  dᵢ≤H : ∀ X Y → dᵢ X Y ≤ℕ H
  dᵢ≤H = MaxLift.bounded (λ _ → S) _ H d≤H

  -------------------------------------
  -- Ultrametric over routing states --
  -------------------------------------
  
  D-ultrametric : Ultrametric _
  D-ultrametric = MaxLift.ultrametric {n = n} (λ _ → _) (λ _ → dᵢ-ultrametric)

  open Ultrametric D-ultrametric public using ()
    renaming
    ( d to D
    ; 0⇒eq to D≡0⇒X≈Y
    ; eq⇒0 to X≈Y⇒D≡0
    ; sym to D-sym
    )

  D≤H : ∀ X Y → D X Y ≤ℕ H
  D≤H = MaxLift.bounded (λ _ → ℝ𝕋ₛ) _ H dᵢ≤H

  d≤D : ∀ X Y i j → d (X i j) (Y i j) ≤ℕ D X Y
  d≤D X Y i j = ≤ℕ-trans (MaxLift.dᵢ≤d (λ _ → S) (λ {i} → d) (X i) (Y i) j) (MaxLift.dᵢ≤d (λ _ → ℝ𝕋ₛ) (λ {i} → dᵢ) X Y i)

  postulate D-witness : ∀ {X Y} → X ≉ₘ Y → ∃₂ λ i j → D X Y ≡ d (X i j) (Y i j) × X i j ≉ Y i j
  --D-witness X≉Y = {!!}
  
  D-image : ∀ X → FiniteImage ℕₛ (D X)
  D-image X = record
    { image    = upTo (suc H)
    ; complete = λ Y → ∈-upTo⁺ (s≤s (D≤H X Y))
    }




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


    DσXσY<DXY : D (σ X) (σ Y) <ℕ D X Y
    DσXσY<DXY with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ X i j
    ... | inj₂ σXᵢⱼ≈Iᵢⱼ           = contradiction σXᵢⱼ≈Iᵢⱼ σXᵢⱼ≉Iᵢⱼ
    ... | inj₁ (k , σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) = begin
      D (σ X) (σ Y)                      ≡⟨ D≡dᵢⱼ ⟩ 
      d (σ X i j) (σ Y i j)              ≤⟨ d-mono σXᵢⱼ≤σYᵢⱼ (σXᵢⱼ≤Aᵢₖ▷Yₖⱼ k , σXᵢⱼ≉Aᵢₖ▷Yₖⱼ k) ⟩
      d (σ X i j) (A i k ▷ Y k j)        ≡⟨ d-cong σXᵢⱼ≈Aᵢₖ▷Xₖⱼ ≈-refl ⟩
      d (A i k ▷ X k j) (A i k ▷ Y k j)  <⟨ d-strContr (A i k) (Xₖⱼ≉Yₖⱼ σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) ⟩
      d (X k j) (Y k j)                  ≤⟨ d≤D X Y k j ⟩
      D X Y                              ∎
      where open Rℕₚ.≤-Reasoning


  abstract

    open PostDisagreementResult using (DσXσY<DXY)
    
    open import RoutingLib.Function.Distance ℝ𝕄ₛ using (_StrContrOver_; _StrContrOnOrbitsOver_)
    open import RoutingLib.Function.Distance.Properties using (strContr⇒strContrOnOrbits)

    σ-strictlyContracting : σ StrContrOver D
    σ-strictlyContracting {X} {Y} Y≉X with σ X ≟ₘ σ Y
    ... | yes σX≈σY = begin
      D (σ X) (σ Y) ≡⟨ X≈Y⇒D≡0 σX≈σY ⟩
      0             <⟨ n≢0⇒0<n (Y≉X ∘ ≈ₘ-sym ∘ D≡0⇒X≈Y) ⟩
      D X Y         ∎
      where open Rℕₚ.≤-Reasoning
    ... | no  σX≉σY with D-witness σX≉σY
    ...   | i , j , D≡dᵢⱼ , σXᵢⱼ≉σYᵢⱼ with ≤-total (σ X i j) (σ Y i j)
    ...     | inj₁ σXᵢⱼ≤σYᵢⱼ = DσXσY<DXY {X} {Y} D≡dᵢⱼ (σXᵢⱼ≤σYᵢⱼ , σXᵢⱼ≉σYᵢⱼ)
    ...     | inj₂ σYᵢⱼ≤σXᵢⱼ = begin
      D (σ X) (σ Y) ≡⟨ D-sym (σ X) (σ Y) ⟩
      D (σ Y) (σ X) <⟨ DσXσY<DXY {Y} {X} (trans (trans (D-sym (σ Y) (σ X)) D≡dᵢⱼ) (d-sym (σ X i j) (σ Y i j))) (σYᵢⱼ≤σXᵢⱼ , σXᵢⱼ≉σYᵢⱼ ∘ ≈-sym) ⟩
      D Y X         ≡⟨ D-sym Y X ⟩
      D X Y         ∎
      where open Rℕₚ.≤-Reasoning
