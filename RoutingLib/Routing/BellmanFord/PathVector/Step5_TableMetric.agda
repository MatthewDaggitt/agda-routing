open import Data.Product using (∃; ∃₂; Σ; _×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s; _<_; _≤_; _≤?_; _∸_; _⊔_; _⊓_; ≤-pred) renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive; m≤m+n; n≤1+n; m+n∸m≡n; n≤m+n; +-mono-≤; ∸-mono;  ⊓-mono-<;+-cancelˡ-≤;  m≤m⊔n; m⊓n≤m; ≰⇒≥; n≤m⊔n; m⊓n≤n; <-transˡ; <-transʳ; +-distribˡ-⊔; <⇒≤)
open import Data.Fin using (Fin)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; subst₂; cong₂)
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
open import RoutingLib.Data.Matrix using (Any; map; min⁺)
open import RoutingLib.Data.Matrix.Properties using (min⁺[M]<min⁺[N])
open import RoutingLib.Data.Table using (Table)
open import RoutingLib.Data.Table.Membership.Propositional.Properties using (max[t]∈t)
open import RoutingLib.Function.Distance using (Ultrametric; IsUltrametric; Bounded; MaxTriangleIneq)
import RoutingLib.Function.Distance.MaxLift as MaxLift

import RoutingLib.Routing.BellmanFord.PathVector.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.PathVector.Step3_InconsistentTableMetric as Step3
import RoutingLib.Routing.BellmanFord.PathVector.Step4_ConsistentTableMetric as Step4

module RoutingLib.Routing.BellmanFord.PathVector.Step5_TableMetric
  {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  {n-1} {𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1)}
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  where

  open Prelude 𝓟𝓢𝓒
  open Step3 𝓟𝓢𝓒
  open Step4 𝓟𝓢𝓒

  Hᶜ : ℕ
  Hᶜ = suc (proj₁ dₜᶜ-bounded)

  Hⁱ : ℕ
  Hⁱ = proj₁ dₜⁱ-bounded

  dₜᶜ<Hᶜ+x : ∀ {x y} (xᶜ : 𝑪ₜ x) (yᶜ : 𝑪ₜ y) z → dₜᶜ xᶜ yᶜ < Hᶜ + z
  dₜᶜ<Hᶜ+x xᶜ yᶜ z = s≤s (≤-trans (proj₂ dₜᶜ-bounded xᶜ yᶜ) (m≤m+n _ z))
  
  --------------------------------
  -- An ultrametric over tables --
  --------------------------------

  dₜ : RTable → RTable → ℕ
  dₜ x y with x ≟ₜ y | 𝑪ₜ? x | 𝑪ₜ? y
  ... | yes _ | _      | _      = zero
  ... | no  _ | yes xᶜ | yes yᶜ = dₜᶜ xᶜ yᶜ
  ... | no  _ | _      | _      = Hᶜ + dₜⁱ x y
  
  dₜ-cong : dₜ Preserves₂ _≈ₜ_ ⟶ _≈ₜ_ ⟶ _≡_
  dₜ-cong {W} {X} {Y} {Z} W≈X Y≈Z with W ≟ₜ Y | X ≟ₜ Z 
  ... | yes _   | yes _   = refl
  ... | yes W≈Y | no  X≉Z = contradiction (≈ₜ-trans (≈ₜ-trans (≈ₜ-sym W≈X) W≈Y) Y≈Z) X≉Z
  ... | no  W≉Y | yes X≈Z = contradiction (≈ₜ-trans (≈ₜ-trans W≈X X≈Z) (≈ₜ-sym Y≈Z)) W≉Y
  ... | no _    | no _    with 𝑪ₜ? W | 𝑪ₜ? X | 𝑪ₜ? Y | 𝑪ₜ? Z
  ...   | no  Wⁱ | yes Xᶜ | _      | _      = contradiction (𝑪ₜ-cong (≈ₜ-sym W≈X) Xᶜ) Wⁱ
  ...   | yes Wᶜ | no  Xⁱ | _      |  _     = contradiction (𝑪ₜ-cong W≈X Wᶜ) Xⁱ
  ...   | _      | _      | yes Yᶜ | no  Zⁱ = contradiction (𝑪ₜ-cong Y≈Z Yᶜ) Zⁱ
  ...   | _      | _      | no  Yⁱ | yes Zᶜ = contradiction (𝑪ₜ-cong (≈ₜ-sym Y≈Z) Zᶜ) Yⁱ
  ...   | no _   | no _   | _      | _      = cong (Hᶜ +_) (dₜⁱ-cong W≈X Y≈Z)
  ...   | yes _  | yes _  | no  _  | no  _  = cong (Hᶜ +_) (dₜⁱ-cong W≈X Y≈Z)
  ...   | yes wᶜ | yes xᶜ | yes yᶜ | yes zᶜ = dₜᶜ-cong wᶜ yᶜ xᶜ zᶜ W≈X Y≈Z

  x≈y⇒dₜ≡0 : ∀ {X Y} → X ≈ₜ Y → dₜ X Y ≡ 0
  x≈y⇒dₜ≡0 {X} {Y} X≈Y with X ≟ₜ Y
  ... | yes _   = refl
  ... | no  X≉Y = contradiction X≈Y X≉Y

  dₜ≡0⇒x≈y : ∀ {X Y} → dₜ X Y ≡ 0 → X ≈ₜ Y
  dₜ≡0⇒x≈y {X} {Y} dₜ≡0 with X ≟ₜ Y
  ... | yes X≈Y = X≈Y
  ... | no  _   with 𝑪ₜ? X | 𝑪ₜ? Y
  ...   | yes Xᶜ | yes Yᶜ  = dₜᶜ≡0⇒x≈y Xᶜ Yᶜ dₜ≡0
  ...   | no  Xⁱ | _      = contradiction dₜ≡0 λ()
  ...   | yes Xᶜ | no  Yⁱ = contradiction dₜ≡0 λ()
  
  dₜ-sym : ∀ X Y → dₜ X Y ≡ dₜ Y X
  dₜ-sym X Y with X ≟ₜ Y | Y ≟ₜ X
  ... | yes _   | yes _   = refl
  ... | yes X≈Y | no  Y≉X = contradiction (≈ₜ-sym X≈Y) Y≉X
  ... | no  X≉Y | yes Y≈X = contradiction (≈ₜ-sym Y≈X) X≉Y
  ... | no _    | no _    with 𝑪ₜ? X | 𝑪ₜ? Y
  ...   | yes Xᶜ | yes Yᶜ = dₜᶜ-sym Xᶜ Yᶜ
  ...   | no  _  | no  _  = cong (Hᶜ +_) (dₜⁱ-sym X Y)
  ...   | no  _  | yes _  = cong (Hᶜ +_) (dₜⁱ-sym X Y)
  ...   | yes _  | no  _  = cong (Hᶜ +_) (dₜⁱ-sym X Y)
  
  dₜ-maxTriIneq-lemma : ∀ X Y Z → Hᶜ + dₜⁱ X Z ≤ (Hᶜ + dₜⁱ X Y) ⊔ (Hᶜ + dₜⁱ Y Z)
  dₜ-maxTriIneq-lemma X Y Z = begin
    Hᶜ + dₜⁱ X Z                    ≤⟨ +-monoʳ-≤ Hᶜ (dₜⁱ-maxTriIneq X Y Z) ⟩
    Hᶜ + (dₜⁱ X Y ⊔ dₜⁱ Y Z)        ≡⟨ +-distribˡ-⊔ Hᶜ _ _ ⟩
    (Hᶜ + dₜⁱ X Y) ⊔ (Hᶜ + dₜⁱ Y Z) ∎
    where open ≤-Reasoning
  
  dₜ-maxTriIneq : MaxTriangleIneq ℝ𝕋ₛ dₜ
  dₜ-maxTriIneq X Y Z with X ≟ₜ Z | X ≟ₜ Y | Y ≟ₜ Z
  dₜ-maxTriIneq X Y Z | yes _   | _       | _       = z≤n
  dₜ-maxTriIneq X Y Z | no  X≉Z | yes X≈Y | yes Y≈Z = contradiction (≈ₜ-trans X≈Y Y≈Z) X≉Z
  dₜ-maxTriIneq X Y Z | no  _   | yes X≈Y | no  _   with 𝑪ₜ? X | 𝑪ₜ? Y | 𝑪ₜ? Z
  ... | yes Xᶜ | yes Yᶜ | yes Zᶜ = ≤-reflexive (dₜᶜ-cong Xᶜ Zᶜ Yᶜ Zᶜ X≈Y ≈ₜ-refl)
  ... | yes Xᶜ | no  Yⁱ | _     = contradiction (𝑪ₜ-cong X≈Y Xᶜ) Yⁱ
  ... | no  Xⁱ | yes Yᶜ | _     = contradiction (𝑪ₜ-cong (≈ₜ-sym X≈Y) Yᶜ) Xⁱ
  ... | yes _  | yes _  | no  _ = +-monoʳ-≤ Hᶜ (≤-reflexive (dₜⁱ-cong X≈Y ≈ₜ-refl))
  ... | no  _  | no  _  | yes _ = +-monoʳ-≤ Hᶜ (≤-reflexive (dₜⁱ-cong X≈Y ≈ₜ-refl))
  ... | no  _  | no  _  | no  _ = +-monoʳ-≤ Hᶜ (≤-reflexive (dₜⁱ-cong X≈Y ≈ₜ-refl))
  dₜ-maxTriIneq X Y Z | no  _   | no  _   | yes Y≈Z with 𝑪ₜ? X | 𝑪ₜ? Y | 𝑪ₜ? Z
  ... | yes Xᶜ | yes Yᶜ | yes Zᶜ = m≤n⇒m≤n⊔o 0 (≤-reflexive (dₜᶜ-cong Xᶜ Zᶜ Xᶜ Yᶜ ≈ₜ-refl (≈ₜ-sym Y≈Z)))
  ... | _      | yes Yᶜ | no  Zⁱ = contradiction (𝑪ₜ-cong Y≈Z Yᶜ) Zⁱ
  ... | _      | no  Yⁱ | yes Zᶜ = contradiction (𝑪ₜ-cong (≈ₜ-sym Y≈Z) Zᶜ) Yⁱ
  ... | no  _  | yes _  | yes _  = m≤n⇒m≤n⊔o 0 (+-monoʳ-≤ Hᶜ (≤-reflexive (dₜⁱ-cong ≈ₜ-refl (≈ₜ-sym Y≈Z))))
  ... | yes _  | no  _  | no  _  = m≤n⇒m≤n⊔o 0 (+-monoʳ-≤ Hᶜ (≤-reflexive (dₜⁱ-cong ≈ₜ-refl (≈ₜ-sym Y≈Z))))
  ... | no  _  | no  _  | no  _  = m≤n⇒m≤n⊔o 0 (+-monoʳ-≤ Hᶜ (≤-reflexive (dₜⁱ-cong ≈ₜ-refl (≈ₜ-sym Y≈Z))))
  dₜ-maxTriIneq X Y Z | no  _   | no  _   | no  _   with 𝑪ₜ? X | 𝑪ₜ? Y | 𝑪ₜ? Z
  ... | yes Xᶜ | yes Yᶜ | yes Zᶜ = dₜᶜ-maxTriIneq Xᶜ Yᶜ Zᶜ
  ... | yes Xᶜ | yes Yᶜ | no  Zⁱ = m≤o⇒m≤n⊔o (dₜᶜ Xᶜ Yᶜ) (+-monoʳ-≤ Hᶜ (XᶜYᶜZⁱ⇒dₜⁱXZ≤dₜⁱYZ Xᶜ Yᶜ Zⁱ))
  ... | no  Xⁱ | yes Yᶜ | yes Zᶜ = m≤n⇒m≤n⊔o (dₜᶜ Yᶜ Zᶜ) (+-monoʳ-≤ Hᶜ (XⁱYᶜZᶜ⇒dₜⁱXZ≤dₜⁱXY Xⁱ Yᶜ Zᶜ))
  ... | yes Xᶜ | no  Yⁱ | yes Zᶜ = m≤n⇒m≤n⊔o (Hᶜ + dₜⁱ Y Z) (<⇒≤ (dₜᶜ<Hᶜ+x Xᶜ Zᶜ _))
  ... | yes _  | no  _  | no  _  = dₜ-maxTriIneq-lemma X Y Z
  ... | no  _  | yes _  | no  _  = dₜ-maxTriIneq-lemma X Y Z
  ... | no  _  | no  _  | yes _  = dₜ-maxTriIneq-lemma X Y Z
  ... | no  _  | no  _  | no  _  = dₜ-maxTriIneq-lemma X Y Z


  Hᶜ+dₜⁱ≤dₜ : ∀ {x y} → 𝑰ₜ x ⊎ 𝑰ₜ y → Hᶜ + dₜⁱ x y ≤ dₜ x y
  Hᶜ+dₜⁱ≤dₜ {x} {y} xⁱ⊎yⁱ with x ≟ₜ y
  ... | yes _ = ?
  ... | no  _ with 𝑪ₜ? x | 𝑪ₜ? y
  ...   | yes xᶜ | yes yᶜ = ?
  ...   | no  _  | no  _  = ?
  ...   | no  _  | yes _  = ?
  ...   | yes _  | no  _  = ?
  
  postulate dₜ-force-𝑪 : ∀ {k} {X Y : RMatrix} (Xₖᶜ : 𝑪ₜ (X k)) (Yₖᶜ : 𝑪ₜ (Y k)) →
                (∀ i → dₜ (X i) (Y i) ≤ dₜᶜ Xₖᶜ Yₖᶜ) →
                Σ (𝑪ₘ X) (λ Xᶜ → Σ (𝑪ₘ Y) (λ Yᶜ → (∀ i → dₜᶜ (Xᶜ i) (Yᶜ i) ≤ dₜᶜ (Xᶜ k) (Yᶜ k))))

  dₜ-force-dₜⁱ : ∀ {X Y : RMatrix} {l} → 
                 (∀ i → dₜ (X i) (Y i) ≤ Hᶜ + dₜⁱ (X l) (Y l)) →
                 (∀ i → 𝑰ₜ (X i) ⊎ 𝑰ₜ (Y i) → dₜⁱ (X i) (Y i) ≤ dₜⁱ (X l) (Y l))
  dₜ-force-dₜⁱ {X} {Y} {l} dₜ≤Hᶜ+dₜⁱXₗYₗ i Xᵢⁱ⊎Yᵢⁱ = +-cancelˡ-≤ Hᶜ (≤-trans (Hᶜ+dₜⁱ≤dₜ Xᵢⁱ⊎Yᵢⁱ) (dₜ≤Hᶜ+dₜⁱXₗYₗ i))
    
  dₜ-strContr-XᶜYᶜ : ∀ {k l X Y} → X l ≉ₜ Y l →
                    (Xᶜ : 𝑪ₘ X) (Yᶜ : 𝑪ₘ Y) → 
                    (∀ i → dₜ (σ X i) (σ Y i) ≤ dₜ (σ X k) (σ Y k)) →
                    (∀ i → dₜᶜ (Xᶜ i) (Yᶜ i)   ≤ dₜᶜ (Xᶜ l) (Yᶜ l)) →
                    dₜ (σ X k) (σ Y k) < dₜᶜ (Xᶜ l) (Yᶜ l)
  dₜ-strContr-XᶜYᶜ {k} {l} {X} {Y} Xₗ≉Yₗ Xᶜ Yᶜ dₜ≤dₜσXₖσYₖ dₜᶜ≤dₜᶜXₗYₗ with σ X k ≟ₜ σ Y k
  ... | yes σXₖ≈σYₖ = n≢0⇒0<n (Xₗ≉Yₗ ∘ dₜᶜ≡0⇒x≈y (Xᶜ l) (Yᶜ l))
  ... | no  _        with 𝑪ₜ? (σ X k) | 𝑪ₜ? (σ Y k)
  ...   | _        | no  σYₖⁱ = contradiction (σ-pres-𝑪ₘ Yᶜ k) σYₖⁱ
  ...   | no  σXₖⁱ | _        = contradiction (σ-pres-𝑪ₘ Xᶜ k) σXₖⁱ
  ...   | yes σXₖᶜ | yes σYₖᶜ with dₜ-force-𝑪 σXₖᶜ σYₖᶜ dₜ≤dₜσXₖσYₖ
  ...     | σXᶜ , σYᶜ , dₜᶜ≤dₜᶜσXₖσYₖ = begin
    dₜᶜ σXₖᶜ    σYₖᶜ    ≡⟨ dₜᶜ-cong σXₖᶜ σYₖᶜ (σXᶜ k) (σYᶜ k) ≈ₜ-refl ≈ₜ-refl  ⟩
    dₜᶜ (σXᶜ k) (σYᶜ k) <⟨ dₜᶜ-strContr Xₗ≉Yₗ Xᶜ Yᶜ σXᶜ σYᶜ dₜᶜ≤dₜᶜσXₖσYₖ dₜᶜ≤dₜᶜXₗYₗ ⟩
    dₜᶜ (Xᶜ l)  (Yᶜ l)  ∎
    where open ≤-Reasoning
    
  dₜ-strContr-XYⁱ : ∀ {k l X Y} →
                    (∀ i → dₜ (X i) (Y i) ≤ Hᶜ + dₜⁱ (X l) (Y l)) →
                    dₜ (σ X k) (σ Y k) < Hᶜ + dₜⁱ (X l) (Y l)
  dₜ-strContr-XYⁱ {k} {l} {X} {Y} dₜ≤dₜXₗYₗ with σ X k ≟ₜ σ Y k
  ... | yes σXₖ≈σYₖ = s≤s z≤n
  ... | no  σXₖ≉σYₖ with 𝑪ₜ? (σ X k) | 𝑪ₜ? (σ Y k)
  ...   | yes σXₖᶜ | yes σYₖᶜ = dₜᶜ<Hᶜ+x σXₖᶜ σYₖᶜ _
  ...   | yes _    | no  σYₖⁱ = +-monoʳ-< Hᶜ (dₜⁱ-strContr (inj₂ σYₖⁱ) (dₜ-force-dₜⁱ dₜ≤dₜXₗYₗ))
  ...   | no  σXₖⁱ | yes _    = +-monoʳ-< Hᶜ (dₜⁱ-strContr (inj₁ σXₖⁱ) (dₜ-force-dₜⁱ dₜ≤dₜXₗYₗ))
  ...   | no  σXₖⁱ | no  _    = +-monoʳ-< Hᶜ (dₜⁱ-strContr (inj₁ σXₖⁱ) (dₜ-force-dₜⁱ dₜ≤dₜXₗYₗ))

  dₜ-strContracting : ∀ {k l X Y} → X l ≉ₜ Y l → 
                      (∀ i → dₜ (σ X i) (σ Y i) ≤ dₜ (σ X k) (σ Y k)) →
                      (∀ i → dₜ (X i) (Y i) ≤ dₜ (X l) (Y l)) →
                      dₜ (σ X k) (σ Y k) < dₜ (X l) (Y l)
  dₜ-strContracting {k} {l} {X} {Y} Xₗ≉Yₗ dₜ≤dₜσXₖσYₖ dₜ≤dₜXₗYₗ with X l ≟ₜ Y l
  ... | yes Xₗ≈Yₗ = contradiction Xₗ≈Yₗ Xₗ≉Yₗ
  ... | no  _     with 𝑪ₜ? (X l) | 𝑪ₜ? (Y l)
  ...   | no  _   | yes _   = dₜ-strContr-XYⁱ dₜ≤dₜXₗYₗ
  ...   | yes _   | no  _   = dₜ-strContr-XYⁱ dₜ≤dₜXₗYₗ
  ...   | no  _   | no  _   = dₜ-strContr-XYⁱ dₜ≤dₜXₗYₗ
  ...   | yes Xₗᶜ | yes Yₗᶜ with dₜ-force-𝑪 Xₗᶜ Yₗᶜ dₜ≤dₜXₗYₗ
  ...     | Xᶜ , Yᶜ , dₜᶜ≤dₜᶜXₖYₖ = begin
    dₜ (σ X k) (σ Y k)  <⟨ dₜ-strContr-XᶜYᶜ Xₗ≉Yₗ Xᶜ Yᶜ dₜ≤dₜσXₖσYₖ dₜᶜ≤dₜᶜXₖYₖ ⟩
    dₜᶜ (Xᶜ l) (Yᶜ l)   ≡⟨ dₜᶜ-cong (Xᶜ l) (Yᶜ l) Xₗᶜ Yₗᶜ ≈ₜ-refl ≈ₜ-refl ⟩
    dₜᶜ Xₗᶜ Yₗᶜ         ∎
    where open ≤-Reasoning

  dₜ≤Hᶜ+Hⁱ : ∀ x y → dₜ x y ≤ Hᶜ + Hⁱ
  dₜ≤Hᶜ+Hⁱ x y with x ≟ₜ y
  ... | yes _ = z≤n
  ... | no  _ with 𝑪ₜ? x | 𝑪ₜ? y
  ...   | yes xᶜ | yes yᶜ = ≤-trans (proj₂ dₜᶜ-bounded xᶜ yᶜ) (≤-trans (n≤1+n _) (m≤m+n Hᶜ Hⁱ))
  ...   | no  _  | no  _  = +-monoʳ-≤ Hᶜ (proj₂ dₜⁱ-bounded x y)
  ...   | no  _  | yes _  = +-monoʳ-≤ Hᶜ (proj₂ dₜⁱ-bounded x y)
  ...   | yes _  | no  _  = +-monoʳ-≤ Hᶜ (proj₂ dₜⁱ-bounded x y)
  
  dₜ-bounded : Bounded ℝ𝕋ₛ dₜ
  dₜ-bounded = Hᶜ + Hⁱ , dₜ≤Hᶜ+Hⁱ
  
  dₜ-isUltrametric : IsUltrametric ℝ𝕋ₛ dₜ
  dₜ-isUltrametric = record
    { cong        = dₜ-cong
    ; eq⇒0        = x≈y⇒dₜ≡0
    ; 0⇒eq        = dₜ≡0⇒x≈y
    ; sym         = dₜ-sym
    ; maxTriangle = dₜ-maxTriIneq
    }

  dₜ-ultrametric : Ultrametric ℝ𝕋ₛ
  dₜ-ultrametric = record
    { d             = dₜ
    ; isUltrametric = dₜ-isUltrametric
    }
