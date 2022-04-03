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
  using (_≡_; _≢_; cong; subst; refl; sym; trans)
import Relation.Binary.Reasoning.PartialOrder as POR
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import RoutingLib.Routing.Basics.Path.CertifiedI.AllVertices
open import RoutingLib.Routing.Basics.Path.CertifiedI.Properties
open import RoutingLib.Data.Fin.Subset using (Nonfull)
open import RoutingLib.Data.Nat.Properties using (+-presˡ-nonZero)

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Prelude using (RoutingMatrix; AdjacencyMatrix)
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.Convergence.Prelude as Prelude
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.Convergence.Step1_NodeSets as Step1_NodeSets
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.Convergence.Step2_ConvergedSubtree as Step2_ConvergedSubtree
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.Convergence.Step3_DangerousNodes as Step3_DangerousNodes

module RoutingLib.Routing.VectorBased.Synchronous.PathVector.Convergence.Step4_InductiveStep
  {a b ℓ n-1} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (isPathAlgebra : IsCertifiedPathAlgebra algebra (suc n-1))
  (A : AdjacencyMatrix algebra (suc n-1))
  (X : RoutingMatrix   algebra (suc n-1))
  (j : Fin (suc n-1))
  (t : ℕ)
  (open Prelude isRoutingAlgebra isPathAlgebra A)
  (open Step1_NodeSets isRoutingAlgebra isPathAlgebra A X j)
  (C : Subset n)
  (C-nonFull : Nonfull C)
  (j∈C : j ∈ C)
  (C⊆𝓒ₜ : ∀ {i} → i ∈ C → i ∈ᵤ 𝓒 t)
  (open Step2_ConvergedSubtree isRoutingAlgebra isPathAlgebra A X j t C C-nonFull j∈C)
  (open Notation X j)
  (tⁱⁿᶜ-1 : ℕ)
  (eₘᵢₙ≤ₜ₊ₜⁱⁿᶜ₊ₛe : ∀ s k → eₘᵢₙ ≤[ t + (tⁱⁿᶜ-1 + s) ] (iₘᵢₙ , k))
  where

kₘᵢₙ∈𝓒ₜ : kₘᵢₙ ∈ᵤ 𝓒 t
kₘᵢₙ∈𝓒ₜ = C⊆𝓒ₜ kₘᵢₙ∈C

open POR ≤₊-poset

-- tⁱⁿᶜ is the time taken for a new node to have provably converged.
--   tⁱⁿᶜ = n for increasing algebras 
--   tⁱⁿᶜ = 1 for increasing and distributive algebras
tⁱⁿᶜ : ℕ
tⁱⁿᶜ = suc tⁱⁿᶜ-1

iₘᵢₙ-pred≤ : ∀ s → A iₘᵢₙ kₘᵢₙ ▷ σ (t + tⁱⁿᶜ-1 + s) X kₘᵢₙ j ≤₊ σ (suc (t + tⁱⁿᶜ-1 + s)) X iₘᵢₙ j
iₘᵢₙ-pred≤ s with FXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ (σ (t + tⁱⁿᶜ-1 + s) X) iₘᵢₙ j
... | inj₂ σXᵢⱼ≈Iᵢⱼ    = begin
  A iₘᵢₙ kₘᵢₙ ▷ σ (t + tⁱⁿᶜ-1 + s) X kₘᵢₙ j  ≤⟨ ≤₊-maximum _ ⟩
  ∞#                                         ≡⟨ sym (Iᵢⱼ≡∞ j≢iₘᵢₙ) ⟩
  I iₘᵢₙ j                                   ≈⟨ ≈-sym σXᵢⱼ≈Iᵢⱼ ⟩
  σ (suc (t + tⁱⁿᶜ-1 + s)) X iₘᵢₙ j          ∎
... | inj₁ (k , σXᵢⱼ≈AᵢₖXₖⱼ) = begin
  A iₘᵢₙ kₘᵢₙ ▷ σ (t + tⁱⁿᶜ-1 + s)   X kₘᵢₙ j  ≡⟨ cong (λ v → A iₘᵢₙ kₘᵢₙ ▷ σ v X kₘᵢₙ j) (+-assoc t tⁱⁿᶜ-1 s) ⟩
  A iₘᵢₙ kₘᵢₙ ▷ σ (t + (tⁱⁿᶜ-1 + s)) X kₘᵢₙ j  ≤⟨ eₘᵢₙ≤ₜ₊ₜⁱⁿᶜ₊ₛe s k ⟩
  A iₘᵢₙ k    ▷ σ (t + (tⁱⁿᶜ-1 + s)) X k    j  ≡⟨ cong (λ v → A iₘᵢₙ k ▷ σ v X k j) (sym (+-assoc t tⁱⁿᶜ-1 s)) ⟩
  A iₘᵢₙ k    ▷ σ (t + tⁱⁿᶜ-1 + s)   X k    j  ≈⟨ ≈-sym σXᵢⱼ≈AᵢₖXₖⱼ ⟩
  σ (suc (t + tⁱⁿᶜ-1 + s)) X iₘᵢₙ j            ∎

iₘᵢₙ-pred : ∀ s → σ (t + tⁱⁿᶜ + s) X iₘᵢₙ j ≈ A iₘᵢₙ kₘᵢₙ ▷ σ (t + (tⁱⁿᶜ-1 + s)) X kₘᵢₙ j
iₘᵢₙ-pred s = begin-equality
  σ (t + tⁱⁿᶜ + s)       X iₘᵢₙ j             ≡⟨ cong (λ v → σ (v + s) X iₘᵢₙ j) (+-suc t tⁱⁿᶜ-1) ⟩
  σ (suc t + tⁱⁿᶜ-1 + s) X iₘᵢₙ j             ≈⟨ ≤₊-antisym (FXᵢⱼ≤Aᵢₖ▷Xₖⱼ (σ (t + tⁱⁿᶜ-1 + s) X) iₘᵢₙ j kₘᵢₙ) (iₘᵢₙ-pred≤ s) ⟩
  A iₘᵢₙ kₘᵢₙ ▷ σ (t + tⁱⁿᶜ-1 + s)   X kₘᵢₙ j ≡⟨ cong (λ v → A iₘᵢₙ kₘᵢₙ ▷ σ v X kₘᵢₙ j) (+-assoc t tⁱⁿᶜ-1 s) ⟩
  A iₘᵢₙ kₘᵢₙ ▷ σ (t + (tⁱⁿᶜ-1 + s)) X kₘᵢₙ j ∎

iₘᵢₙ∈𝓕ₜ₊ₜⁱⁿᶜ : iₘᵢₙ ∈ᵤ 𝓕 (t + tⁱⁿᶜ)
iₘᵢₙ∈𝓕ₜ₊ₜⁱⁿᶜ s = begin-equality
  σ (t + tⁱⁿᶜ + s) X iₘᵢₙ j                    ≈⟨ iₘᵢₙ-pred s ⟩
  A iₘᵢₙ kₘᵢₙ ▷ σ (t + (tⁱⁿᶜ-1 + s)) X kₘᵢₙ j  ≈⟨ ▷-cong (A iₘᵢₙ kₘᵢₙ) (𝓒-eq t kₘᵢₙ (tⁱⁿᶜ-1 + s) (tⁱⁿᶜ-1 + 0) kₘᵢₙ∈𝓒ₜ) ⟩ 
  A iₘᵢₙ kₘᵢₙ ▷ σ (t + (tⁱⁿᶜ-1 + 0)) X kₘᵢₙ j  ≈⟨ ≈-sym (iₘᵢₙ-pred 0) ⟩
  σ (t + tⁱⁿᶜ + 0) X iₘᵢₙ j                    ≡⟨ cong (λ v → σ v X iₘᵢₙ j) (+-identityʳ (t + tⁱⁿᶜ)) ⟩
  σ (t + tⁱⁿᶜ)     X iₘᵢₙ j                    ∎

private
  lemma₄ : ∀ {p} → path (σ (t + tⁱⁿᶜ) X iₘᵢₙ j) ≡ p →
           path (A iₘᵢₙ kₘᵢₙ ▷ σ (t + tⁱⁿᶜ-1) X kₘᵢₙ j) ≈ₚ p
  lemma₄ {p} refl = path-cong (begin-equality
    A iₘᵢₙ kₘᵢₙ ▷ σ (t + tⁱⁿᶜ-1)       X kₘᵢₙ j  ≡⟨ cong (λ v → A iₘᵢₙ kₘᵢₙ ▷ σ (t + v) X kₘᵢₙ j) (sym (+-identityʳ tⁱⁿᶜ-1)) ⟩
    A iₘᵢₙ kₘᵢₙ ▷ σ (t + (tⁱⁿᶜ-1 + 0)) X kₘᵢₙ j  ≈⟨ ≈-sym (iₘᵢₙ-pred 0) ⟩
    σ (t + tⁱⁿᶜ + 0) X iₘᵢₙ j                    ≡⟨ cong (λ v → σ v X iₘᵢₙ j) (+-identityʳ (t + tⁱⁿᶜ)) ⟩
    σ (t + tⁱⁿᶜ) X iₘᵢₙ j                        ∎)

p[iₘᵢₙ]∈𝓕ₜ₊ₜⁱⁿᶜ : Allᵥ (𝓕 (t + tⁱⁿᶜ)) (path (σ (t + tⁱⁿᶜ) X iₘᵢₙ j))
p[iₘᵢₙ]∈𝓕ₜ₊ₜⁱⁿᶜ with path (σ (t + tⁱⁿᶜ) X iₘᵢₙ j) in p[σᵗ⁺ᵗⁱⁿᶜ]≡iₘk∷p
... | invalid                     = invalid
... | trivial                     = trivial
... | valid ((_ , _) ∷ p ∣ _ ∣ _) with ▷-alignment (A iₘᵢₙ kₘᵢₙ) (σ (t + tⁱⁿᶜ-1) X kₘᵢₙ j) (lemma₄ p[σᵗ⁺ᵗⁱⁿᶜ]≡iₘk∷p)
...   | refl , refl , p[σᵗ⁺ᵗⁱⁿᶜ⁻¹Xₖⱼ]≈p with 𝓒ₜ⊆𝓒ₜ₊ₛ t tⁱⁿᶜ kₘᵢₙ∈𝓒ₜ 
...     | (k∈S , pₖ∈S) with Allᵥ-resp-≈ₚ pₖ∈S (≈ₚ-trans (path-cong (𝓒-eq t _ tⁱⁿᶜ tⁱⁿᶜ-1 kₘᵢₙ∈𝓒ₜ)) p[σᵗ⁺ᵗⁱⁿᶜ⁻¹Xₖⱼ]≈p) 
...       | valid p∈S = valid ([ iₘᵢₙ∈𝓕ₜ₊ₜⁱⁿᶜ , k∈S ]∷ p∈S)

iₘᵢₙ∈𝓒ₜ₊ₜⁱⁿᶜ : iₘᵢₙ ∈ᵤ 𝓒 (t + tⁱⁿᶜ)
iₘᵢₙ∈𝓒ₜ₊ₜⁱⁿᶜ = iₘᵢₙ∈𝓕ₜ₊ₜⁱⁿᶜ , p[iₘᵢₙ]∈𝓕ₜ₊ₜⁱⁿᶜ
