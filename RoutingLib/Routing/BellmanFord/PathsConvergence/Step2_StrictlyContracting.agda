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
open import RoutingLib.Routing.BellmanFord.PathsConvergence.SufficientConditions
open import RoutingLib.Routing.BellmanFord.GeneralConvergence.SufficientConditions using () renaming (SufficientConditions to GeneralSufficientConditions)
open import RoutingLib.Data.Nat.Properties using (m≤n⇒m≤n⊔o; m≤o⇒m≤n⊔o; n<m⇒n⊓o<m; n≤m⇒n⊓o≤m)
open import RoutingLib.Data.Matrix using (Any; map; min⁺)
open import RoutingLib.Data.Matrix.Properties using (min⁺[M]<min⁺[N])
import RoutingLib.Routing.BellmanFord.PathsConvergence.Prelude as Prelude

module RoutingLib.Routing.BellmanFord.PathsConvergence.Step2_StrictlyContracting
  {a b ℓ}
  (𝓡𝓐 : RoutingAlgebra a b ℓ)
  (sc : SufficientConditions 𝓡𝓐)
  {n-1 : ℕ} 
  (G : Graph (RoutingAlgebra.Step 𝓡𝓐) (suc n-1))
  where

  open SufficientConditions sc
  open Prelude 𝓡𝓐 ⊕-sel G

  open import RoutingLib.Routing.BellmanFord.GeneralConvergence.Step2_UltrametricAlt 𝓡𝓟ᶜ (convertSufficientConditions sc) using () renaming (d to dᶜ; dₘₐₓ to dᶜₘₐₓ; d≡0⇒X≈Y to dᶜ≡0⇒X≈Y; d-sym to dᶜ-sym; d-cong₂ to dᶜ-cong; d-maxTriIneq to dᶜ-maxTriIneq; d≤dₘₐₓ to dᶜ≤dᶜₘₐₓ)
  open import RoutingLib.Routing.BellmanFord.GeneralConvergence.Step3_StrictlyContracting 𝓡𝓟ᶜ (convertSufficientConditions sc) using () renaming (σ-strictlyContracting to σᶜ-strContrOver-dᶜ)
  
  open import RoutingLib.Routing.BellmanFord.PathsConvergence.Step1_Ultrametric 𝓡𝓐 sc G
  open import RoutingLib.Function.Distance ℝ𝕄ⁱₛ using (_StrContrOver_)

  abstract
  
    test₃ : ∀ X i j (σXᵢⱼⁱ : 𝑰 (σⁱ X i j)) →
            lengthⁱ (X (𝒊-parent X i j σXᵢⱼⁱ) j) < sizeⁱ (σⁱ X i j)
    test₃ X i j ¬σXᵢⱼᶜ = begin
      suc (lengthⁱ (X (𝒊-parent X i j ¬σXᵢⱼᶜ) j)) ≡⟨ cong suc (lengthⁱ≡size[r] (𝒊-parentⁱ X i j ¬σXᵢⱼᶜ)) ⟩
      suc (sizeⁱ (X (𝒊-parent X i j ¬σXᵢⱼᶜ) j))   ≡⟨ ≡-sym (𝒊-parent-size X i j ¬σXᵢⱼᶜ) ⟩
      sizeⁱ (σⁱ X i j)                           ∎
      where open ≤-Reasoning

    lengthⁱ-inc : ∀ X → 𝑰ₘ (σⁱ X) → ∀ i j → ∃₂ λ k l → lengthⁱ (X k l) < lengthⁱ (σⁱ X i j)
    lengthⁱ-inc X σXⁱ i j with 𝑪? (σⁱ X i j) | 𝑰ₘ-witness σXⁱ
    ... | no  σXᵢⱼⁱ | _              = 𝒊-parent X i j σXᵢⱼⁱ , j , test₃ X i j σXᵢⱼⁱ
    ... | yes σXᵢⱼᶜ  | k , l , σXₖₗⁱ = 𝒊-parent X k l σXₖₗⁱ , l , <-transˡ (test₃ X k l σXₖₗⁱ) (sizeⁱ≤n-1 (σⁱ X k l))
      
    σⁱ-strContr-sh : ∀ X → 𝑰ₘ (σⁱ X) → shortest X < shortest (σⁱ X) 
    σⁱ-strContr-sh X σXⁱ = min⁺[M]<min⁺[N] (lengthⁱ-inc X σXⁱ)

    σⁱ-strContr-sh⊓sh : ∀ X Y → 𝑰ₘ (σⁱ X) ⊎ 𝑰ₘ (σⁱ Y) → shortest X ⊓ shortest Y < shortest (σⁱ X) ⊓ shortest (σⁱ Y)
    σⁱ-strContr-sh⊓sh X Y (inj₁ σXⁱ) with 𝑪ₘ? Y | 𝑪ₘ? (σⁱ Y)
    ... | yes Yᶜ | _       = subst₂ _<_ (≡-sym (Yᶜ⇒shX⊓shY≡shX X Yᶜ)) (≡-sym (Yᶜ⇒shX⊓shY≡shX (σⁱ X) (σⁱ-pres-𝑪ₘ Yᶜ))) (σⁱ-strContr-sh X σXⁱ)
    ... | no  Yⁱ | yes σYᶜ = subst (shortest X ⊓ shortest Y <_) (≡-sym (Yᶜ⇒shX⊓shY≡shX (σⁱ X) σYᶜ)) (<-transʳ (m⊓n≤m (shortest X) (shortest Y)) (σⁱ-strContr-sh X σXⁱ))
    ... | no  Yⁱ | no  σYⁱ = ⊓-mono-< (σⁱ-strContr-sh X σXⁱ) (σⁱ-strContr-sh Y σYⁱ)
    σⁱ-strContr-sh⊓sh X Y (inj₂ σYⁱ) with 𝑪ₘ? X | 𝑪ₘ? (σⁱ X)
    ... | yes Xᶜ | _       = subst₂ _<_ (≡-sym (Xᶜ⇒shX⊓shY≡shY Y Xᶜ)) (≡-sym (Xᶜ⇒shX⊓shY≡shY (σⁱ Y) (σⁱ-pres-𝑪ₘ Xᶜ))) (σⁱ-strContr-sh Y σYⁱ)
    ... | no  Xⁱ | yes σXᶜ = subst (shortest X ⊓ shortest Y <_) (≡-sym (Xᶜ⇒shX⊓shY≡shY (σⁱ Y) σXᶜ)) (<-transʳ (m⊓n≤n (shortest X) (shortest Y)) (σⁱ-strContr-sh Y σYⁱ))
    ... | no  Xⁱ | no  σXⁱ = ⊓-mono-< (σⁱ-strContr-sh X σXⁱ) (σⁱ-strContr-sh Y σYⁱ)


    σⁱ-strContr-dᶜ : ∀ {X Y} → Y ≉ⁱₘ X →
                     (Xᶜ : 𝑪ₘ X) (σXᶜ : 𝑪ₘ (σⁱ X))
                     (Yᶜ : 𝑪ₘ Y) (σYᶜ : 𝑪ₘ (σⁱ Y)) →
                     dᶜ (fromIₘ σXᶜ) (fromIₘ σYᶜ) < dᶜ (fromIₘ Xᶜ) (fromIₘ Yᶜ)
    σⁱ-strContr-dᶜ Y≉X Xᶜ σXᶜ Yᶜ σYᶜ = subst
      (_< dᶜ (fromIₘ Xᶜ) (fromIₘ Yᶜ))
      (≡-sym (dᶜ-cong (σ-fromIₘ-commute Xᶜ σXᶜ) (σ-fromIₘ-commute Yᶜ σYᶜ)))
      (σᶜ-strContrOver-dᶜ (fromIₘ-¬cong Yᶜ Xᶜ Y≉X))
      
    σⁱ-strContr-dⁱ : ∀ X Y → 𝑰ₘ (σⁱ X) ⊎ 𝑰ₘ (σⁱ Y) → dⁱ (σⁱ X) (σⁱ Y) < dⁱ X Y
    σⁱ-strContr-dⁱ X Y σXⁱ⊎σYⁱ =
      invert-< (σⁱ-strContr-sh⊓sh X Y σXⁱ⊎σYⁱ) (shX⊓shY<n (σⁱ X) (σⁱ Y))
    
    σⁱ-strContr-dₕ : σⁱ StrContrOver dₕ
    σⁱ-strContr-dₕ {X} {Y} Y≉X with 𝑪ₘ? X | 𝑪ₘ? (σⁱ X) | 𝑪ₘ? Y |  𝑪ₘ? (σⁱ Y)
    ... | yes Xᶜ | no  σXⁱ | _      | _       = contradiction (σⁱ-pres-𝑪ₘ Xᶜ) σXⁱ
    ... | _      | _       | yes Yᶜ | no  σYⁱ = contradiction (σⁱ-pres-𝑪ₘ Yᶜ) σYⁱ
    ... | yes _  | yes σXᶜ | no  _  | yes σYᶜ  = dᶜ<dⁱ _ _ X Y
    ... | no  _  | yes σXᶜ | yes _  | yes σYᶜ  = dᶜ<dⁱ _ _ X Y
    ... | no  _  | yes σXᶜ | no  _  | yes σYᶜ  = dᶜ<dⁱ _ _ X Y
    ... | no  _  | no  σXⁱ | yes _  | yes _   = σⁱ-strContr-dⁱ X Y (inj₁ σXⁱ)
    ... | no  _  | no  σXⁱ | no  _  | yes _   = σⁱ-strContr-dⁱ X Y (inj₁ σXⁱ)
    ... | no  _  | no  σXⁱ | no  _  | no  _   = σⁱ-strContr-dⁱ X Y (inj₁ σXⁱ)
    ... | no  _  | yes _   | no  _  | no  σYⁱ = σⁱ-strContr-dⁱ X Y (inj₂ σYⁱ)
    ... | yes _  | yes _   | no  _  | no  σYⁱ = σⁱ-strContr-dⁱ X Y (inj₂ σYⁱ)
    ... | yes Xᶜ | yes σXᶜ | yes Yᶜ  | yes σYᶜ = σⁱ-strContr-dᶜ Y≉X Xᶜ _ _ _

    σⁱ-strContr-d : σⁱ StrContrOver d
    σⁱ-strContr-d {X} {Y} Y≉X with X ≟ⁱₘ Y | σⁱ X ≟ⁱₘ σⁱ Y
    ... | no _    | no  _ = σⁱ-strContr-dₕ Y≉X
    ... | no _    | yes _ = X≉Y⇒0<dₕ (Y≉X ∘ ≈ⁱₘ-sym)
    ... | yes X≈Y | _     = contradiction (≈ⁱₘ-sym X≈Y) Y≉X
