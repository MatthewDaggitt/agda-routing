open import Data.Fin using (Fin; zero)
open import Data.Sum using (inj₁; inj₂)
open import Data.Nat using (ℕ; suc; zero; z≤n; s≤s; _≤_; _<_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import RoutingLib.Data.Matrix using (SquareMatrix)
open import RoutingLib.Data.Table using (Table; max; zipWith)
open import RoutingLib.Data.Table.Properties using (max[t]<x)
open import RoutingLib.Data.Table.Membership.Propositional.Properties using (max[t]∈t)
open import RoutingLib.Data.Nat.Properties using (ℕₛ; n≢0⇒0<n; module ≤-Reasoning)
open import RoutingLib.Function.Metric using (Ultrametric; IsUltrametric; Bounded)
import RoutingLib.Function.Metric.MaxLift as MaxLift

open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.BellmanFord.AsyncConvergence.DistanceVector.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.AsyncConvergence.DistanceVector.Step2_RouteMetric as Step2
open FiniteStrictlyIncreasingRoutingAlgebra using (Step)

module RoutingLib.Routing.BellmanFord.AsyncConvergence.DistanceVector.Step3_StateMetric
  {a b ℓ n} (algebra : FiniteStrictlyIncreasingRoutingAlgebra a b ℓ)
  (A : SquareMatrix (Step algebra) n)
  where
  
open Prelude algebra A
open Step2 algebra A using
  ( d
  ; x≈y⇒d≡0
  ; d≡0⇒x≈y
  ; d-isUltrametric
  ; d-bounded
  ; d-strContr
  )

open import RoutingLib.Function.Metric ℝ𝕄ₛ
  using (_StrContrOver_; _StrContrOnOrbitsOver_; _StrContrOnFixedPointOver_)

-------------------------------------
-- Ultrametric over routing tables --
-------------------------------------

dₜ : RTable → RTable → ℕ
dₜ x y = max 0 (zipWith d x y)

dₜ-isUltrametric : IsUltrametric _ dₜ
dₜ-isUltrametric = MaxLift.isUltrametric {n = n} _ d-isUltrametric

dₜ-bounded : Bounded ℝ𝕋ₛ dₜ
dₜ-bounded = MaxLift.bounded ℝ𝕋ₛⁱ d-bounded

-------------------------------------
-- Ultrametric over routing states --
-------------------------------------

D : RMatrix → RMatrix → ℕ
D X Y = max 0 (zipWith dₜ X Y)

D-isUltrametric : IsUltrametric _ D
D-isUltrametric = MaxLift.isUltrametric {n = n} _ dₜ-isUltrametric

D-bounded : Bounded ℝ𝕄ₛ D
D-bounded = MaxLift.bounded ℝ𝕄ₛⁱ dₜ-bounded

open IsUltrametric D-isUltrametric public using ()
  renaming
  ( 0⇒eq to D≡0⇒X≈Y
  ; eq⇒0 to X≈Y⇒D≡0
  ; cong to D-cong
  )

σ-strContr : σ StrContrOver D
σ-strContr {X} {Y} Y≉X with max[t]∈t 0 (λ i → dₜ (X i) (Y i))
... | inj₁ dXY≡0            = contradiction (D≡0⇒X≈Y dXY≡0) (Y≉X ∘ ≈ₘ-sym)
... | inj₂ (r , DXY≡dₜXᵣYᵣ) with max[t]∈t 0 (λ i → d (X r i) (Y r i))
...   | inj₁ dXᵣYᵣ≡0              = contradiction (D≡0⇒X≈Y (trans DXY≡dₜXᵣYᵣ dXᵣYᵣ≡0)) (Y≉X ∘ ≈ₘ-sym)
...   | inj₂ (s , dXᵣYᵣ≡dᵣXᵣₛYᵣₛ) = begin
  D  (σ X)   (σ Y)   <⟨ DσXσY<dXᵣₛYᵣₛ ⟩
  d (X r s) (Y r s)  ≡⟨ sym DXY≈dᵣXᵣₛYᵣₛ ⟩
  D  X       Y       ∎
  where
  open ≤-Reasoning

  DXY≈dᵣXᵣₛYᵣₛ : D X Y ≡ d (X r s) (Y r s)
  DXY≈dᵣXᵣₛYᵣₛ = trans DXY≡dₜXᵣYᵣ dXᵣYᵣ≡dᵣXᵣₛYᵣₛ

  Xᵣₛ≉Yᵣₛ : X r s ≉ Y r s
  Xᵣₛ≉Yᵣₛ Xᵣₛ≈Yᵣₛ = Y≉X (≈ₘ-sym (D≡0⇒X≈Y (trans DXY≈dᵣXᵣₛYᵣₛ (x≈y⇒d≡0 Xᵣₛ≈Yᵣₛ))))

  dᵣ≤dᵣXᵣₛYᵣₛ : ∀ u v → X u v ≉ Y u v → d (X u v) (Y u v) ≤ d (X r s) (Y r s)
  dᵣ≤dᵣXᵣₛYᵣₛ u v _ = begin
    d (X u v) (Y u v) ≤⟨ MaxLift.dᵢ≤d ℝ𝕋ₛⁱ d (X u) (Y u) v ⟩
    dₜ (X u)   (Y u)  ≤⟨ MaxLift.dᵢ≤d ℝ𝕄ₛⁱ dₜ X (Y) u ⟩
    D X (Y)           ≡⟨ DXY≈dᵣXᵣₛYᵣₛ ⟩
    d (X r s) (Y r s) ∎

  0<dᵣXᵣₛYᵣₛ : 0 < d (X r s) (Y r s)
  0<dᵣXᵣₛYᵣₛ = n≢0⇒0<n (Xᵣₛ≉Yᵣₛ ∘ d≡0⇒x≈y)

  DσXσY<dXᵣₛYᵣₛ : D (σ X) (σ Y) < d (X r s) (Y r s)
  DσXσY<dXᵣₛYᵣₛ = max[t]<x {t = zipWith dₜ (σ X) (σ Y)}
           (λ i → max[t]<x {t = zipWith d (σ X i) (σ Y i)}
             (λ j → d-strContr Xᵣₛ≉Yᵣₛ dᵣ≤dᵣXᵣₛYᵣₛ i j)
             0<dᵣXᵣₛYᵣₛ)
           0<dᵣXᵣₛYᵣₛ

σ-strContrOnFP : σ StrContrOnFixedPointOver D
σ-strContrOnFP {X} {X*} σX*≈X* X≉X* = begin
  D X*     (σ X) ≡⟨ D-cong (≈ₘ-sym σX*≈X*) (≈ₘ-refl {x = σ X}) ⟩
  D (σ X*) (σ X) <⟨ σ-strContr X≉X* ⟩
  D X*     X     ∎
  where open ≤-Reasoning
