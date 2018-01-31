open import Data.Fin using (Fin; zero)
open import Data.List using (List)
open import Data.List.Any.Membership.Propositional using (_∈_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Nat using (ℕ; suc; zero; z≤n; s≤s; _⊔_; _*_; _∸_; _≤_; _<_)
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
open import RoutingLib.Data.Table.Properties using (max[t]<x)
open import RoutingLib.Data.Table.Membership.Propositional.Properties using (max[t]∈t)
open import RoutingLib.Data.Nat.Properties as Rℕₚ using (ℕₛ; n≢0⇒0<n; module ≤-Reasoning)
open import RoutingLib.Function.Distance using (IsUltrametric; MaxTriangleIneq)
open import RoutingLib.Data.Matrix using (Matrix)
open import RoutingLib.Data.Matrix.Properties using (max⁺-cong; M≤max⁺[M]; max⁺[M]≡x; max⁺[M]≤x; max⁺-constant; zipWith-sym)
open import RoutingLib.Data.Matrix.Membership.Propositional.Properties using (max⁺[M]∈M)
open import RoutingLib.Data.Matrix.Relation.Pointwise using (zipWith-cong)
import RoutingLib.Function.Distance.MaxLift as MaxLift

open import RoutingLib.Routing.Definitions using (RoutingProblem; RoutingAlgebra)
open import RoutingLib.Routing.BellmanFord.DistanceVector.SufficientConditions
open import RoutingLib.Function.Distance using (Ultrametric; Bounded)
import RoutingLib.Routing.BellmanFord.DistanceVector.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.DistanceVector.Step2_RouteMetric as Step2
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
    ; d≤H
    ; d-ultrametric
    ; d-bounded
    
    ; d-strContr
    )


  -------------------------------------
  -- Ultrametric over routing tables --
  -------------------------------------

  dᵢ-ultrametric : Ultrametric _
  dᵢ-ultrametric = MaxLift.ultrametric {n = n} (λ _ → S) (λ _ → d-ultrametric)

  open Ultrametric dᵢ-ultrametric public using ()
    renaming
    ( d to dᵢ
    ; cong to dᵢ-cong
    ; sym  to dᵢ-sym
    ; eq⇒0 to x≈y⇒dᵢ≡0
    ; 0⇒eq to dᵢ≡0⇒x≈y
    ; maxTriangle to dᵢ-maxTriIneq 
    ; isUltrametric to dᵢ-isUltrametric
    )

  dᵢ-bounded : Bounded ℝ𝕋ₛ dᵢ
  dᵢ-bounded = MaxLift.bounded (λ _ → S) d d-bounded

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
    ; cong to D-cong
    )

  D-bounded : Bounded ℝ𝕄ₛ D
  D-bounded = MaxLift.bounded (λ _ → ℝ𝕋ₛ) _ dᵢ-bounded

  d≤D : ∀ X Y i j → d (X i j) (Y i j) ≤ D X Y
  d≤D X Y i j = ≤ℕ-trans (MaxLift.dᵢ≤d (λ _ → S) (λ {i} → d) (X i) (Y i) j) (MaxLift.dᵢ≤d (λ _ → ℝ𝕋ₛ) (λ {i} → dᵢ) X Y i)



  open import RoutingLib.Function.Distance ℝ𝕄ₛ using (_StrContrOver_; _StrContrOnOrbitsOver_)
  open import RoutingLib.Function.Distance.Properties using (strContr⇒strContrOnOrbits)

  σ-strContr : σ StrContrOver D
  σ-strContr {X} {Y} Y≉X with max[t]∈t 0 (λ i → dᵢ (X i) (Y i))
  ... | inj₁ dXY≡0              = contradiction (D≡0⇒X≈Y dXY≡0) (Y≉X ∘ ≈ₘ-sym)
  ... | inj₂ (r , DXY≡dₜXᵣYᵣ) with max[t]∈t 0 (λ i → d (X r i) (Y r i))
  ...   | inj₁ dXᵣYᵣ≡0               = contradiction (D≡0⇒X≈Y (trans DXY≡dₜXᵣYᵣ dXᵣYᵣ≡0)) (Y≉X ∘ ≈ₘ-sym)
  ...   | inj₂ (s , dXᵣYᵣ≡dᵣXᵣₛYᵣₛ) = begin
    D  (σ X)   (σ Y)   <⟨ test ⟩
    d (X r s) (Y r s) ≡⟨ sym DXY≈dᵣXᵣₛYᵣₛ ⟩
    D  X       Y       ∎
    where
    open ≤-Reasoning

    DXY≈dᵣXᵣₛYᵣₛ : D X Y ≡ d (X r s) (Y r s)
    DXY≈dᵣXᵣₛYᵣₛ = trans DXY≡dₜXᵣYᵣ dXᵣYᵣ≡dᵣXᵣₛYᵣₛ
    
    Xᵣₛ≉Yᵣₛ : X r s ≉ Y r s
    Xᵣₛ≉Yᵣₛ Xᵣₛ≈Yᵣₛ = Y≉X (≈ₘ-sym (D≡0⇒X≈Y (trans DXY≈dᵣXᵣₛYᵣₛ (x≈y⇒d≡0 Xᵣₛ≈Yᵣₛ))))

    dᵣ≤dᵣXᵣₛYᵣₛ : ∀ u v → X u v ≉ Y u v → d (X u v) (Y u v) ≤ d (X r s) (Y r s)
    dᵣ≤dᵣXᵣₛYᵣₛ u v _ = begin
      d (X u v) (Y u v) ≤⟨ MaxLift.dᵢ≤d (λ _ → S) d (X u) (Y u) v ⟩
      dᵢ (X u)   (Y u)   ≤⟨ MaxLift.dᵢ≤d (λ _ → ℝ𝕋ₛ) dᵢ X (Y) u ⟩
      D X (Y)           ≡⟨ DXY≈dᵣXᵣₛYᵣₛ ⟩
      d (X r s) (Y r s) ∎

    0<dᵣXᵣₛYᵣₛ : 0 < d (X r s) (Y r s)
    0<dᵣXᵣₛYᵣₛ = n≢0⇒0<n (Xᵣₛ≉Yᵣₛ ∘ d≡0⇒x≈y)
    
    test : D (σ X) (σ Y) < d (X r s) (Y r s)
    test = max[t]<x {t = zipWith dᵢ (σ X) (σ Y)}
             (λ i → max[t]<x {t = zipWith d (σ X i) (σ Y i)}
               (λ j → d-strContr Xᵣₛ≉Yᵣₛ dᵣ≤dᵣXᵣₛYᵣₛ i j)
               0<dᵣXᵣₛYᵣₛ)
             0<dᵣXᵣₛYᵣₛ
