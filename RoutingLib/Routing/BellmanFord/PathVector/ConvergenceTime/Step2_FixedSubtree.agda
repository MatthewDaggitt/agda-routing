open import Data.Fin using (Fin)
open import Data.Fin.Dec using (_∈?_)
open import Data.Fin.Subset using (Subset; _∈_; _∉_; _∪_; Nonempty)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using (List)
open import Data.List.All using (lookup)
open import Relation.Unary using () renaming (_∈_ to _∈ᵤ_)
import Relation.Binary.PartialOrderReasoning as POR
open import Relation.Binary.PropositionalEquality
  using (refl; _≢_; subst)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Fin.Subset using (Nonfull)
open import RoutingLib.Data.Fin.Subset.Cutset
open import RoutingLib.Data.List using (allFinPairs)
import RoutingLib.Data.List.Extrema as Extrema
open import RoutingLib.Data.SimplePath hiding (_∈_; _∉_)
open import RoutingLib.Data.SimplePath.Relation.Equality
open import RoutingLib.Data.SimplePath.All

open import RoutingLib.Routing.Definitions
open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions
import RoutingLib.Routing.BellmanFord.PathVector.ConvergenceTime.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.PathVector.ConvergenceTime.Step1_NodeSets as Step1_NodeSets

module RoutingLib.Routing.BellmanFord.PathVector.ConvergenceTime.Step2_FixedSubtree
  {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  {n-1}   {𝓡𝓟 : RoutingProblem 𝓡𝓐 n-1}
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  (X : RoutingProblem.RMatrix 𝓡𝓟)
  (j : Fin (suc n-1))
  (t-1 : ℕ)
  {F : Subset (suc n-1)}
  (j∈F : j ∈ F)
  (F-nonFull : Nonfull F)
  (F-fixed : ∀ {i} → i ∈ F → i ∈ᵤ Step1_NodeSets.Fixed 𝓟𝓢𝓒 X j (suc t-1))
  where

  open Prelude 𝓟𝓢𝓒
  open Notation X j
  open Step1_NodeSets 𝓟𝓢𝓒 X j
  
  open Extrema ≤₊-totalOrder
  
  private
  
    t : ℕ
    t = suc t-1

    e↷F⇒w[t+s]≡w[t] : ∀ {e} → e ↷ F → ∀ s → weightₑ (t + s) e ≈ weightₑ t e
    e↷F⇒w[t+s]≡w[t] (_ , k∈F) s = ▷-cong (A _ _) (proj₁ (F-fixed k∈F) s)
  
  ------------------------------------------------------------------------------
  -- Finding the fixed minimal edge entering the fixed set

  -- At least one edge entering the fixed set exists
  
    eₐ : Edge
    eₐ = (proj₁ F-nonFull , j)

    eₐ↷F : eₐ ↷ F
    eₐ↷F = (proj₂ F-nonFull , j∈F)

  -- We can therefore find the minimum weight edge out of the fixed set
  
  abstract
  
    eₘᵢₙ : Edge
    eₘᵢₙ = argmin (weightₑ t) eₐ (cutset F)

    eₘᵢₙ↷F : eₘᵢₙ ↷ F
    eₘᵢₙ↷F = argmin-all (weightₑ t) eₐ↷F (∈cutset⇒↷ F)
    
  iₘᵢₙ : Node
  iₘᵢₙ = proj₁ eₘᵢₙ

  iₘᵢₙ∉F : iₘᵢₙ ∉ F
  iₘᵢₙ∉F = proj₁ eₘᵢₙ↷F
    
  kₘᵢₙ : Node
  kₘᵢₙ = proj₂ eₘᵢₙ

  kₘᵢₙ∈F : kₘᵢₙ ∈ F
  kₘᵢₙ∈F = proj₂ eₘᵢₙ↷F
  
  ------------------------------------------------------------------------------
  -- Properties of eₘᵢₙ
  
  abstract

    j≢iₘᵢₙ : j ≢ iₘᵢₙ
    j≢iₘᵢₙ j≡iₘᵢₙ = iₘᵢₙ∉F (subst (_∈ F) j≡iₘᵢₙ j∈F)

    kₘᵢₙ∈Fₜ : kₘᵢₙ ∈ᵤ Fixed t
    kₘᵢₙ∈Fₜ = F-fixed kₘᵢₙ∈F
  
    -- Any edge that cuts the fixed set is -always- less than the minimum edge
    eₘᵢₙ-isMinₜ₊ₛ : ∀ {e} → e ↷ F → ∀ s →
                    weightₑ (t + s) eₘᵢₙ ≤₊ weightₑ (t + s) e
    eₘᵢₙ-isMinₜ₊ₛ {e} e↷F s = begin
      weightₑ (t + s) eₘᵢₙ  ≈⟨ e↷F⇒w[t+s]≡w[t] eₘᵢₙ↷F s ⟩
      weightₑ t       eₘᵢₙ  ≤⟨ lookup (f[argmin]≤f[xs] eₐ (cutset F)) (↷⇒∈cutset e↷F) ⟩
      weightₑ t       e     ≈⟨ ≈-sym (e↷F⇒w[t+s]≡w[t] e↷F s) ⟩
      weightₑ (t + s) e     ∎
      where open POR ≤₊-poset



    -- Any "real" route ending in a node outside of the fixed set is worse
    -- than that ending with the minimal edge.

  private
    lemma₁ : ∀ {i k l s} → σ^ (t + s) X k j ≈ A k l ▷ σ^ (t + s) X l j →
            eₘᵢₙ ≤[ t + s ] (k , l) → eₘᵢₙ ≤[ t + s ] (i , k)
    lemma₁ {i} {k} {l} {s} eq leq = begin
      A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + s) X kₘᵢₙ j         ≤⟨ leq ⟩
      A k    l    ▷ σ^ (t + s) X l j           ≤⟨ ⊕-absorbs-▷ (A i k) _ ⟩
      A i    k    ▷ (A k l ▷ σ^ (t + s) X l j) ≈⟨ ▷-cong (A i k) (≈-sym eq) ⟩
      A i    k    ▷ σ^ (t + s) X k j           ∎
      where open POR ≤₊-poset
   
  ∈Real-invalid : ∀ s {i k} →
                  path (σ^ (t + s) X k j) ≈ₚ invalid →
                  eₘᵢₙ ≤[ t + s ] (i , k)
  ∈Real-invalid s {i} {k} p[σᵗ⁺ˢXₖⱼ]≈∅ = begin
    A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + s) X kₘᵢₙ j ≤⟨ ⊕-identityˡ _ ⟩
    0#                               ≈⟨ ≈-sym (▷-zero (A i k)) ⟩
    A i    k    ▷ 0#                 ≈⟨ ▷-cong (A i k) (≈-sym (path[r]≈∅⇒r≈0 p[σᵗ⁺ˢXₖⱼ]≈∅)) ⟩
    A i    k    ▷ σ^ (t + s) X k j   ∎
    where open POR ≤₊-poset

  ∈Real-trivial : ∀ s {i k} → k ∉ F →
                  path (σ^ (t + s) X k j) ≈ₚ valid [] →
                  eₘᵢₙ ≤[ t + s ] (i , k)
  ∈Real-trivial s {i} {k} k∉F p[σᵗ⁺ˢXₖⱼ]≈[]
    with p[σXᵢⱼ]≈[]⇒i≡j (σ^ (t-1 + s) X) k j p[σᵗ⁺ˢXₖⱼ]≈[]
  ... | refl = contradiction j∈F k∉F
  
  ∈Real : ∀ s i {k} → k ∈ᵤ Real (t + s) → k ∉ F →
          ∀ {p} → path (σ^ (t + s) X k j) ≈ₚ p →
          eₘᵢₙ ≤[ t + s ] (i , k)
  ∈Real s i _      _    {invalid}  p[σᵗ⁺ˢXₖⱼ]≈∅  = ∈Real-invalid s p[σᵗ⁺ˢXₖⱼ]≈∅
  ∈Real s i k∈Rₛ₊ₜ k∉F {valid []} p[σᵗ⁺ˢXₖⱼ]≈[] = ∈Real-trivial s k∉F p[σᵗ⁺ˢXₖⱼ]≈[]
  ∈Real s i k∈Rₛ₊ₜ k∉F {valid ((_ , l) ∷ p ∣ _ ∣ _)} p[σᵗ⁺ˢXₖⱼ]≈kl∷p
    with Real-path {t-1 + s} p[σᵗ⁺ˢXₖⱼ]≈kl∷p k∈Rₛ₊ₜ
  ... | valid ([ _ , l∈Rₛ₊ₜ ]∷ _)
    with Real-alignment (t-1 + s) k∈Rₛ₊ₜ p[σᵗ⁺ˢXₖⱼ]≈kl∷p
  ...   | refl , σᵗ⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢXₗⱼ , p[σᵗ⁺ˢXₗⱼ]≈p with l ∈? F
  ...     | yes l∈F = lemma₁ σᵗ⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢXₗⱼ (eₘᵢₙ-isMinₜ₊ₛ (k∉F , l∈F) s)
  ...     | no  l∉F = lemma₁ σᵗ⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢXₗⱼ (∈Real s _ l∈Rₛ₊ₜ l∉F p[σᵗ⁺ˢXₗⱼ]≈p)
