open import Data.Product using (∃; ∃₂; _×_; _,_)
open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s; _<_; _≤_; _≤?_; _∸_; _⊔_; _⊓_; ≤-pred)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive; m≤m+n; m+n∸m≡n; +-mono-≤; ∸-mono; ⊓-mono-<; m≤m⊔n; m⊓n≤m; ≰⇒≥; n≤m⊔n; m⊓n≤n; <-transˡ; <-transʳ; module ≤-Reasoning)
open import Data.Fin using (Fin)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; subst; subst₂; cong₂) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Algebra.FunctionProperties
open import RoutingLib.Data.Graph
open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions
open import RoutingLib.Routing.BellmanFord.DistanceVector.SufficientConditions using () renaming (SufficientConditions to GeneralSufficientConditions)
open import RoutingLib.Data.Nat.Properties using (m≤n⇒m≤n⊔o; m≤o⇒m≤n⊔o; n<m⇒n⊓o<m; n≤m⇒n⊓o≤m)
open import RoutingLib.Data.Matrix using (Any; map; min⁺)
open import RoutingLib.Data.Matrix.Properties using (min⁺[M]<min⁺[N])

import RoutingLib.Routing.BellmanFord.PathVector.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.DistanceVector.Step2_Ultrametric as Step2ᶜ
import RoutingLib.Routing.BellmanFord.DistanceVector.Step3_StrictlyContracting as Step3ᶜ

module RoutingLib.Routing.BellmanFord.PathVector.Step3_StrictlyContracting
  {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  {n-1} {𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1)}
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  where

  open Prelude 𝓟𝓢𝓒

  open Step2ᶜ 𝓡𝓟ᶜ 𝓢𝓒 using () renaming
    ( d            to dᶜ
    ; d-cong₂      to dᶜ-cong
    )
  open Step3ᶜ 𝓡𝓟ᶜ 𝓢𝓒 using () renaming
    ( σ-strictlyContracting to σᶜ-strContrOver-dᶜ )
  
  open import RoutingLib.Routing.BellmanFord.PathVector.Step2_Ultrametric 𝓟𝓢𝓒
  open import RoutingLib.Function.Distance ℝ𝕄ₛ using (_StrContrOver_)

  abstract
  
    |Xₖⱼ|<|σXᵢⱼ| : ∀ X i j (σXᵢⱼⁱ : 𝑰 (σ X i j)) →
                   lengthⁱ (X (𝒊-parent X i j σXᵢⱼⁱ) j) < size (σ X i j)
    |Xₖⱼ|<|σXᵢⱼ| X i j σXᵢⱼⁱ with 𝑪? (X (𝒊-parent X i j σXᵢⱼⁱ) j)
    ... | yes Xₖⱼᶜ = contradiction Xₖⱼᶜ (𝒊-parentⁱ X i j σXᵢⱼⁱ)
    ... | no  _    = ≤-reflexive (≡-sym (𝒊-parent-size X i j σXᵢⱼⁱ))

    lengthⁱ-inc : ∀ {X} → 𝑰ₘ (σ X) → ∀ i j → ∃₂ λ k l → lengthⁱ (X k l) < lengthⁱ (σ X i j)
    lengthⁱ-inc {X} σXⁱ i j with 𝑪? (σ X i j)
    ... | no  σXᵢⱼⁱ = 𝒊-parent X i j σXᵢⱼⁱ , j , |Xₖⱼ|<|σXᵢⱼ| X i j σXᵢⱼⁱ
    ... | yes σXᵢⱼᶜ with 𝑰ₘ-witness σXⁱ
    ...   | k , l , σXₖₗⁱ = 𝒊-parent X k l σXₖₗⁱ , l , <-transˡ (|Xₖⱼ|<|σXᵢⱼ| X k l σXₖₗⁱ) (≤-pred (size<n (σ X k l)))
    
    σ-strContr-sh : ∀ {X} → 𝑰ₘ (σ X) → shortest X < shortest (σ X) 
    σ-strContr-sh {X} σXⁱ = min⁺[M]<min⁺[N] (lengthⁱ-inc σXⁱ)

    σ-strContr-sh⊓sh : ∀ X Y → 𝑰ₘ (σ X) ⊎ 𝑰ₘ (σ Y) → shortest X ⊓ shortest Y < shortest (σ X) ⊓ shortest (σ Y)
    σ-strContr-sh⊓sh X Y (inj₁ σXⁱ) with 𝑪ₘ? (σ Y)
    ... | yes σYᶜ = subst (shortest X ⊓ shortest Y <_) (≡-sym (Yᶜ⇒shX⊓shY≡shX (σ X) σYᶜ)) (<-transʳ (m⊓n≤m (shortest X) (shortest Y)) (σ-strContr-sh σXⁱ))
    ... | no  σYⁱ = ⊓-mono-< (σ-strContr-sh σXⁱ) (σ-strContr-sh σYⁱ)
    σ-strContr-sh⊓sh X Y (inj₂ σYⁱ) with 𝑪ₘ? (σ X)
    ... | yes σXᶜ = subst (shortest X ⊓ shortest Y <_) (≡-sym (Xᶜ⇒shX⊓shY≡shY (σ Y) σXᶜ)) (<-transʳ (m⊓n≤n (shortest X) (shortest Y)) (σ-strContr-sh σYⁱ))
    ... | no  σXⁱ = ⊓-mono-< (σ-strContr-sh σXⁱ) (σ-strContr-sh σYⁱ)

    
    σ-strContr-dⁱ : ∀ X Y → 𝑰ₘ (σ X) ⊎ 𝑰ₘ (σ Y) → dⁱ (σ X) (σ Y) < dⁱ X Y
    σ-strContr-dⁱ X Y σXⁱ⊎σYⁱ =
      invert-< (σ-strContr-sh⊓sh X Y σXⁱ⊎σYⁱ) (shX⊓shY<n (σ X) (σ Y))

    σ-strContr-dᶜ : ∀ {X Y} → Y ≉ₘ X →
                     (Xᶜ : 𝑪ₘ X) (σXᶜ : 𝑪ₘ (σ X))
                     (Yᶜ : 𝑪ₘ Y) (σYᶜ : 𝑪ₘ (σ Y)) →
                     dᶜ (toCMatrix σXᶜ) (toCMatrix σYᶜ) < dᶜ (toCMatrix Xᶜ) (toCMatrix Yᶜ)
    σ-strContr-dᶜ Y≉X Xᶜ σXᶜ Yᶜ σYᶜ = subst
      (_< dᶜ (toCMatrix Xᶜ) (toCMatrix Yᶜ))
      (≡-sym (dᶜ-cong (σ-toCMatrix-commute Xᶜ σXᶜ) (σ-toCMatrix-commute Yᶜ σYᶜ)))
      (σᶜ-strContrOver-dᶜ Y≉X)
      
    σ-strContr-dₕ : σ StrContrOver dₕ
    σ-strContr-dₕ {X} {Y} Y≉X with 𝑪ₘ? X | 𝑪ₘ? Y | 𝑪ₘ? (σ X) | 𝑪ₘ? (σ Y)
    ... | yes Xᶜ | _      | no  σXⁱ | _       = contradiction (σ-pres-𝑪ₘ Xᶜ) σXⁱ
    ... | _      | yes Yᶜ | _       | no  σYⁱ = contradiction (σ-pres-𝑪ₘ Yᶜ) σYⁱ
    ... | yes _  | no  _  | yes σXᶜ | yes σYᶜ  = dᶜ<dⁱ _ _ X Y
    ... | no  _  | _      | yes σXᶜ | yes σYᶜ  = dᶜ<dⁱ _ _ X Y
    ... | no  _  | _      | no  σXⁱ | _       = σ-strContr-dⁱ X Y (inj₁ σXⁱ)
    ... | no  _  | _      | yes _   | no  σYⁱ = σ-strContr-dⁱ X Y (inj₂ σYⁱ)
    ... | yes _  | no  _  | yes _   | no  σYⁱ = σ-strContr-dⁱ X Y (inj₂ σYⁱ)
    ... | yes Xᶜ | yes Yᶜ  | yes σXᶜ | yes σYᶜ = σ-strContr-dᶜ Y≉X Xᶜ _ _ _

    σ-strContr-d : σ StrContrOver d
    σ-strContr-d {X} {Y} Y≉X with X ≟ₘ Y | σ X ≟ₘ σ Y
    ... | no _    | no  _ = σ-strContr-dₕ Y≉X
    ... | no _    | yes _ = X≉Y⇒0<dₕ (Y≉X ∘ ≈ₘ-sym)
    ... | yes X≈Y | _     = contradiction (≈ₘ-sym X≈Y) Y≉X
