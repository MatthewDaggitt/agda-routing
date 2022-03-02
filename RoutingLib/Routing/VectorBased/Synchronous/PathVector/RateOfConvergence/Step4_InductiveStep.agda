open import Data.Nat using (ℕ; NonZero; zero; suc; z≤n; s≤s; _+_; _∸_; _<_; _≤_)
open import Data.Nat.Properties using (+-identityʳ; +-suc; +-assoc; ≤-reflexive; <⇒≱; <-transˡ; m≤m+n; module ≤-Reasoning)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Subset using (Subset; _∈_; _∉_; _∪_)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (_,_; _×_; ∃; ∃₂; proj₁; proj₂)
open import Function using (_∘_)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using () renaming (_∈_ to _∈ᵤ_; _∉_ to _∉ᵤ_; _⊆_ to _⊆ᵤ_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; cong; subst; refl; sym; trans; inspect; [_])
import Relation.Binary.Reasoning.PartialOrder as POR
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import RoutingLib.Routing.Basics.Path.CertifiedI.All
open import RoutingLib.Routing.Basics.Path.CertifiedI.Properties
open import RoutingLib.Data.Fin.Subset using (Nonfull)
open import RoutingLib.Data.Nat.Properties using (+-presˡ-nonZero)

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Prelude using (RoutingMatrix; AdjacencyMatrix)
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Prelude as Prelude
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Step1_NodeSets as Step1_NodeSets
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Step2_ConvergedSubtree as Step2_ConvergedSubtree
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Step3_DangerousNodes as Step3_DangerousNodes

module RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Step4_InductiveStep
  {a b ℓ n-1} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (isPathAlgebra : IsCertifiedPathAlgebra algebra (suc n-1))
  (isIncreasing : IsIncreasing algebra)
  (A : AdjacencyMatrix algebra (suc n-1))
  (X : RoutingMatrix   algebra (suc n-1))
  (j : Fin (suc n-1))
  (open Step1_NodeSets isRoutingAlgebra isPathAlgebra A X j)
  (t : ℕ)
  .{{t≢0 : NonZero t}}
  (converged : ProvablyConvergedSubset t)
  where

open Prelude isRoutingAlgebra isPathAlgebra A
open Notation X j
open POR ≤₊-poset
open Step2_ConvergedSubtree isRoutingAlgebra isPathAlgebra isIncreasing A X j t converged
open Step3_DangerousNodes   isRoutingAlgebra isPathAlgebra isIncreasing A X j t converged

open ProvablyConvergedSubset converged

------------------------------------------------------------------------
-- eₘᵢₙ is the best candidate route at time t + (n-1 + s)

eₘᵢₙ≤ₜ₊ₙ₋₁₊ₛe : ∀ s k → eₘᵢₙ ≤[ t + (n-1 + s) ] (iₘᵢₙ , k)
eₘᵢₙ≤ₜ₊ₙ₋₁₊ₛe s k with 𝓡? (t + (n-1 + s)) k | k ∈? C
... | _        | yes k∈C = eₘᵢₙ-isMinₜ₊ₛ (iₘᵢₙ∉C , k∈C) (n-1 + s)
... | yes k∈𝓡 | no  k∉C = ∈𝓡 (n-1 + s) iₘᵢₙ {{+-presˡ-nonZero t (n-1 + s)}} ≈ₚ-refl k∈𝓡 k∉C
... | no  k∉𝓡 | no _     with eₘᵢₙ ≤[ t + (n-1 + s) ]? (iₘᵢₙ , k)
...   | yes eₘᵢₙ≤e = eₘᵢₙ≤e
...   | no  eₘᵢₙ≰e = contradiction
  (𝓓-length (n-1 + s) (k∉𝓡 , (iₘᵢₙ , ≰₊⇒>₊ eₘᵢₙ≰e)))
  (<⇒≱ (<-transˡ (lengthₑ<n (t + (n-1 + s)) (iₘᵢₙ , k)) (m≤m+n n s)))


iₘᵢₙ-pred≤ : ∀ s → A iₘᵢₙ kₘᵢₙ ▷ σ (t + n-1 + s) X kₘᵢₙ j ≤₊ σ (suc (t + n-1 + s)) X iₘᵢₙ j
iₘᵢₙ-pred≤ s with FXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ (σ (t + n-1 + s) X) iₘᵢₙ j
... | inj₂ σXᵢⱼ≈Iᵢⱼ    = begin
  A iₘᵢₙ kₘᵢₙ ▷ σ (t + n-1 + s) X kₘᵢₙ j  ≤⟨ ≤₊-maximum _ ⟩
  ∞#                                      ≡⟨ sym (Iᵢⱼ≡∞ j≢iₘᵢₙ) ⟩
  I iₘᵢₙ j                                ≈⟨ ≈-sym σXᵢⱼ≈Iᵢⱼ ⟩
  σ (suc (t + n-1 + s)) X iₘᵢₙ j          ∎
... | inj₁ (k , σXᵢⱼ≈AᵢₖXₖⱼ) = begin
  A iₘᵢₙ kₘᵢₙ ▷ σ (t + n-1 + s)   X kₘᵢₙ j  ≡⟨ cong (λ v → A iₘᵢₙ kₘᵢₙ ▷ σ v X kₘᵢₙ j) (+-assoc t n-1 s) ⟩
  A iₘᵢₙ kₘᵢₙ ▷ σ (t + (n-1 + s)) X kₘᵢₙ j  ≤⟨ eₘᵢₙ≤ₜ₊ₙ₋₁₊ₛe s k ⟩
  A iₘᵢₙ k    ▷ σ (t + (n-1 + s)) X k    j  ≡⟨ cong (λ v → A iₘᵢₙ k ▷ σ v X k j) (sym (+-assoc t n-1 s)) ⟩
  A iₘᵢₙ k    ▷ σ (t + n-1 + s)   X k    j  ≈⟨ ≈-sym σXᵢⱼ≈AᵢₖXₖⱼ ⟩
  σ (suc (t + n-1 + s)) X iₘᵢₙ j            ∎

iₘᵢₙ-pred : ∀ s → σ (t + n + s) X iₘᵢₙ j ≈ A iₘᵢₙ kₘᵢₙ ▷ σ (t + (n-1 + s)) X kₘᵢₙ j
iₘᵢₙ-pred s = begin-equality
  σ (t + n + s) X iₘᵢₙ j                   ≡⟨ cong (λ v → σ (v + s) X iₘᵢₙ j) (+-suc t n-1) ⟩
  σ (suc t + n-1 + s) X iₘᵢₙ j             ≈⟨ ≤₊-antisym (FXᵢⱼ≤Aᵢₖ▷Xₖⱼ
                                              (σ (t + n-1 + s) X) iₘᵢₙ j kₘᵢₙ) (iₘᵢₙ-pred≤ s) ⟩
  A iₘᵢₙ kₘᵢₙ ▷ σ (t + n-1 + s) X kₘᵢₙ j   ≡⟨ cong (λ v → A iₘᵢₙ kₘᵢₙ ▷ σ v X kₘᵢₙ j) (+-assoc t n-1 s) ⟩
  A iₘᵢₙ kₘᵢₙ ▷ σ (t + (n-1 + s)) X kₘᵢₙ j ∎

iₘᵢₙ∈𝓕ₜ₊ₙ : iₘᵢₙ ∈ᵤ 𝓕 (t + n)
iₘᵢₙ∈𝓕ₜ₊ₙ s = begin-equality
  σ (t + n + s) X iₘᵢₙ j                    ≈⟨ iₘᵢₙ-pred s ⟩
  A iₘᵢₙ kₘᵢₙ ▷ σ (t + (n-1 + s)) X kₘᵢₙ j  ≈⟨ ▷-cong (A iₘᵢₙ kₘᵢₙ)
                                                (𝓒-eq t kₘᵢₙ (n-1 + s) (n-1 + 0) kₘᵢₙ∈𝓒ₜ) ⟩
  A iₘᵢₙ kₘᵢₙ ▷ σ (t + (n-1 + 0)) X kₘᵢₙ j  ≈⟨ ≈-sym (iₘᵢₙ-pred 0) ⟩
  σ (t + n + 0) X iₘᵢₙ j                    ≡⟨ cong (λ v → σ v X iₘᵢₙ j) (+-identityʳ (t + n)) ⟩
  σ (t + n)     X iₘᵢₙ j                    ∎



private

  lemma₄ : ∀ {p} → path (σ (t + n) X iₘᵢₙ j) ≡ p →
           path (A iₘᵢₙ kₘᵢₙ ▷ σ (t + n-1) X kₘᵢₙ j) ≈ₚ p
  lemma₄ {p} refl = path-cong (begin-equality
    A iₘᵢₙ kₘᵢₙ ▷ σ (t + n-1)     X kₘᵢₙ j    ≡⟨ cong (λ v → A iₘᵢₙ kₘᵢₙ ▷ σ (t + v) X kₘᵢₙ j) (sym (+-identityʳ n-1)) ⟩
    A iₘᵢₙ kₘᵢₙ ▷ σ (t + (n-1 + 0)) X kₘᵢₙ j  ≈⟨ ≈-sym (iₘᵢₙ-pred 0) ⟩
    σ (t + n + 0) X iₘᵢₙ j                    ≡⟨ cong (λ v → σ v X iₘᵢₙ j) (+-identityʳ (t + n)) ⟩
    σ (t + n) X iₘᵢₙ j                        ∎)

p[iₘᵢₙ]∈𝓕ₜ₊ₙ : Allᵥ (𝓕 (t + n)) (path (σ (t + n) X iₘᵢₙ j))
p[iₘᵢₙ]∈𝓕ₜ₊ₙ with path (σ (t + n) X iₘᵢₙ j) | inspect path (σ (t + n) X iₘᵢₙ j)
... | invalid                     | _ = invalid
... | trivial                     | _ = trivial
... | valid ((_ , _) ∷ p ∣ _ ∣ _) | [ p[σᵗ⁺ⁿ]≡iₘk∷p ]
  with alignPathExtension (σ (t + n-1) X) iₘᵢₙ j kₘᵢₙ (lemma₄ p[σᵗ⁺ⁿ]≡iₘk∷p)
...   | refl , refl , p[σᵗ⁺ⁿ⁻¹Xₖⱼ]≈p with 𝓒ₜ⊆𝓒ₜ₊ₛ t n kₘᵢₙ∈𝓒ₜ
...     | (k∈S , pₖ∈S) with Allᵥ-resp-≈ₚ pₖ∈S (≈ₚ-trans (path-cong (𝓒-eq t _ n n-1 kₘᵢₙ∈𝓒ₜ)) p[σᵗ⁺ⁿ⁻¹Xₖⱼ]≈p)
...       | valid p∈S = valid ([ iₘᵢₙ∈𝓕ₜ₊ₙ , k∈S ]∷ p∈S)

iₘᵢₙ∈𝓒ₜ₊ₙ : iₘᵢₙ ∈ᵤ 𝓒 (t + n)
iₘᵢₙ∈𝓒ₜ₊ₙ = iₘᵢₙ∈𝓕ₜ₊ₙ , p[iₘᵢₙ]∈𝓕ₜ₊ₙ
