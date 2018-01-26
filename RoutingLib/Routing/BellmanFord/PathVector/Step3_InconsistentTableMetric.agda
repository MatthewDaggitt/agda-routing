open import Data.Product using (∃; ∃₂; Σ; _×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s; _<_; _≤_; _≤?_; _∸_; _⊔_; _⊓_; ≤-pred) renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive; m≤m+n; m+n∸m≡n; +-mono-≤; ∸-mono;  ⊓-mono-<; ⊔-mono-≤; m≤m⊔n; m⊓n≤m; ≰⇒≥; <⇒≢; n≤m⊔n; m⊓n≤n; <-transˡ; <-transʳ; +-distribˡ-⊔)
open import Data.Fin using (Fin)
open import Data.Sum using (_⊎_; inj₁; inj₂; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂; cong₂)
open import Relation.Binary using (_Preserves₂_⟶_⟶_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Algebra.FunctionProperties
open import RoutingLib.Data.Graph
open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions
open import RoutingLib.Routing.BellmanFord.DistanceVector.SufficientConditions using () renaming (SufficientConditions to GeneralSufficientConditions)
open import RoutingLib.Data.Nat.Properties using (m≤n⇒m≤n⊔o; m≤o⇒m≤n⊔o; n<m⇒n⊓o<m; n≤m⇒n⊓o≤m; m<n⇒n≢0; ≤-stepsʳ; +-monoʳ-≤; +-monoʳ-<; n≢0⇒0<n; module ≤-Reasoning)
open import RoutingLib.Data.Table using (Table; max⁺; zipWith)
open import RoutingLib.Data.Table.Properties using (t≤max⁺[t]; max⁺-cong; max⁺[t]≤x)
open import RoutingLib.Data.Table.Membership.Propositional.Properties using (max⁺[t]∈t)
import RoutingLib.Function.Distance as Distance 
import RoutingLib.Function.Distance.MaxLift as MaxLift

import RoutingLib.Routing.BellmanFord.PathVector.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.PathVector.Step2_InconsistentRouteMetric as Step2

module RoutingLib.Routing.BellmanFord.PathVector.Step3_InconsistentTableMetric
  {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  {n-1} {𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1)}
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  where

  open Prelude 𝓟𝓢𝓒
  open Step2 𝓟𝓢𝓒
  open Distance ℝ𝕋ₛ using (Ultrametric; Bounded; MaxTriangleIneq)

  dₜⁱ : RTable → RTable → ℕ
  dₜⁱ x y = max⁺ (zipWith dᵣⁱ x y)

  dₜⁱ-cong : dₜⁱ Preserves₂ _≈ₜ_ ⟶ _≈ₜ_ ⟶ _≡_
  dₜⁱ-cong x≈y u≈v = max⁺-cong (λ i → dᵣⁱ-cong (x≈y i) (u≈v i))
  
  dₜⁱ-sym : ∀ x y → dₜⁱ x y ≡ dₜⁱ y x
  dₜⁱ-sym x y = max⁺-cong (λ i → dᵣⁱ-sym (x i) (y i))

  dₜⁱ-maxTriIneq : MaxTriangleIneq dₜⁱ
  dₜⁱ-maxTriIneq x y z with max⁺[t]∈t (zipWith dᵣⁱ x z)
  ... | i , dₜⁱ≡dᵣⁱxᵢzⁱ = begin
    dₜⁱ x z                           ≡⟨ dₜⁱ≡dᵣⁱxᵢzⁱ ⟩
    dᵣⁱ (x i) (z i)                   ≤⟨ dᵣⁱ-maxTriIneq _ _ _ ⟩
    dᵣⁱ (x i) (y i) ⊔ dᵣⁱ (y i) (z i) ≤⟨ ⊔-mono-≤ (t≤max⁺[t] _ i) (t≤max⁺[t] _ i) ⟩
    dₜⁱ x y ⊔ dₜⁱ y z                 ∎
    where open ≤-Reasoning

  dₜⁱ-bounded : Bounded dₜⁱ
  dₜⁱ-bounded with dᵣⁱ-bounded
  ... | (v , dᵣⁱ≤v) = (v , λ x y → max⁺[t]≤x (λ i → dᵣⁱ≤v (x i) (y i)))


  postulate XⁱYᶜZᶜ⇒dₜⁱXZ≤dₜⁱXY : ∀ {X Y Z} → 𝑰ₜ X → 𝑪ₜ Y → 𝑪ₜ Z → dₜⁱ X Z ≤ dₜⁱ X Y
  --XⁱYᶜZᶜ⇒dₜⁱXZ≤dₜⁱXY Xⁱ Yᶜ Zᶜ = {!!}
    --≤-reflexive (trans (XⁱYᶜ⇒DⁱXY≡DⁱX Xⁱ Zᶜ) (sym (XⁱYᶜ⇒DⁱXY≡DⁱX Xⁱ Yᶜ)))
    
  XᶜYᶜZⁱ⇒dₜⁱXZ≤dₜⁱYZ : ∀ {X Y Z} → 𝑪ₜ X → 𝑪ₜ Y → 𝑰ₜ Z → dₜⁱ X Z ≤ dₜⁱ Y Z
  XᶜYᶜZⁱ⇒dₜⁱXZ≤dₜⁱYZ {X} {Y} {Z} Xᶜ Yᶜ Zⁱ =
    subst₂ _≤_ (dₜⁱ-sym Z X) (dₜⁱ-sym Z Y) (XⁱYᶜZᶜ⇒dₜⁱXZ≤dₜⁱXY Zⁱ Yᶜ Xᶜ)


  

  dₜⁱ-force-𝑰 : ∀ {x y i} → dₜⁱ x y ≡ dᵣⁱ (x i) (y i) → 𝑰ₜ x ⊎ 𝑰ₜ y → 𝑰 (x i) ⊎ 𝑰 (y i)
  dₜⁱ-force-𝑰 {x} {y} {i} dₜⁱxy≡dᵣⁱxᵢyᵢ xⁱ⊎yⁱ with 𝑪? (x i) | 𝑪? (y i)
  ... | no  xᵢⁱ | _       = inj₁ xᵢⁱ
  ... | _       | no  yᵢⁱ = inj₂ yᵢⁱ
  ... | yes xᵢᶜ | yes yᵢᶜ with map 𝑰ₜ-witness 𝑰ₜ-witness xⁱ⊎yⁱ
  ...   | inj₁ (j , xⱼⁱ) = contradiction (sym dₜⁱxy≡dᵣⁱxᵢyᵢ) (<⇒≢ (<-transˡ (dᵣⁱ-mono-𝑰𝑪 xᵢᶜ yᵢᶜ (inj₁ xⱼⁱ)) (t≤max⁺[t] _ j)))
  ...   | inj₂ (j , yⱼⁱ) = contradiction (sym dₜⁱxy≡dᵣⁱxᵢyᵢ) (<⇒≢ (<-transˡ (dᵣⁱ-mono-𝑰𝑪 xᵢᶜ yᵢᶜ (inj₂ yⱼⁱ)) (t≤max⁺[t] _ j)))

  dₜⁱ-force-≤ :  ∀ {X Y : RMatrix} {r s} →
                 dₜⁱ (X r) (Y r) ≡ dᵣⁱ (X r s) (Y r s) →
                 (∀ s  → 𝑰ₜ (X s) ⊎ 𝑰ₜ (Y s) → dₜⁱ (X s) (Y s) ≤ dₜⁱ (X r) (Y r)) →
                 ∀ k l → 𝑰 (X k l) ⊎ 𝑰 (Y k l) → dᵣⁱ (X k l) (Y k l) ≤ dᵣⁱ (X r s) (Y r s)
  dₜⁱ-force-≤ {X} {Y} {r} {s} dₜⁱXᵣYᵣ≡dᵣⁱXᵣₛYᵣₛ dₜⁱ≤dᵣⁱXᵣₛYᵣₛ k l Xₖₗⁱ⊎Yₖₗ = begin
    dᵣⁱ (X k l) (Y k l)   ≤⟨ t≤max⁺[t] _ l ⟩
    dₜⁱ (X k)   (Y k)     ≤⟨ dₜⁱ≤dᵣⁱXᵣₛYᵣₛ k (map 𝑰⇒𝑰ₜ 𝑰⇒𝑰ₜ Xₖₗⁱ⊎Yₖₗ) ⟩
    dₜⁱ (X r)   (Y r)     ≡⟨ dₜⁱXᵣYᵣ≡dᵣⁱXᵣₛYᵣₛ ⟩
    dᵣⁱ (X r s) (Y r s)   ∎
    where open ≤-Reasoning
    
  dₜⁱ-strContr : ∀ {i r X Y} → 𝑰ₜ (σ X i) ⊎ 𝑰ₜ (σ Y i) →
                 (∀ s → 𝑰ₜ (X s) ⊎ 𝑰ₜ (Y s) → dₜⁱ (X s) (Y s) ≤ dₜⁱ (X r) (Y r)) →
                 dₜⁱ (σ X i) (σ Y i) < dₜⁱ (X r) (Y r)
  dₜⁱ-strContr {i} {r} {X} {Y} σXₖⁱ⊎σYₖⁱ dₜⁱ≤dₜⁱXᵣYᵣ
    with max⁺[t]∈t (λ j → dᵣⁱ (X r j) (Y r j))
       | max⁺[t]∈t (λ j → dᵣⁱ (σ X i j) (σ Y i j))
  ... | s , dₜⁱ≡dᵣXᵣₛYᵣₛ | j , dₜⁱ≡dᵣσXᵢⱼσYᵢⱼ = begin
    dₜⁱ (σ X i)  (σ Y i)          ≡⟨ dₜⁱ≡dᵣσXᵢⱼσYᵢⱼ ⟩
    dᵣⁱ (σ X i j) (σ Y i j)        <⟨ dᵣⁱ-strContr {i} {j} {r} {s} {X} {Y}
                                      (dₜⁱ-force-𝑰 dₜⁱ≡dᵣσXᵢⱼσYᵢⱼ σXₖⁱ⊎σYₖⁱ)
                                      (dₜⁱ-force-≤ dₜⁱ≡dᵣXᵣₛYᵣₛ dₜⁱ≤dₜⁱXᵣYᵣ) ⟩
    dᵣⁱ (X r s)   (Y r s)          ≡⟨ sym dₜⁱ≡dᵣXᵣₛYᵣₛ ⟩
    dₜⁱ (X r)     (Y r)            ∎
    where open ≤-Reasoning

  
