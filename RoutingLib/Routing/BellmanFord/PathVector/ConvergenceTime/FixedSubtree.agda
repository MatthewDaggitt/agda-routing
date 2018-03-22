open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; _∈_; _∉_; _∪_; Nonempty)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using (List)
open import Data.List.All using (lookup)
open import Relation.Unary
  using () renaming (_∈_ to _∈ᵤ_)
import Relation.Binary.PartialOrderReasoning as PartialOrderReasoning
import Relation.Binary.EqReasoning as EqReasoning

open import RoutingLib.Data.Fin.Subset using (Nonfull)
open import RoutingLib.Data.Fin.Subset.Cutset
open import RoutingLib.Data.List using (allFinPairs)
import RoutingLib.Data.List.Extrema as Extrema

open import RoutingLib.Routing.Definitions
open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions
import RoutingLib.Routing.BellmanFord.PathVector.ConvergenceTime.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.PathVector.ConvergenceTime.NodeSets as NodeSets

module RoutingLib.Routing.BellmanFord.PathVector.ConvergenceTime.FixedSubtree
  {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  {n-1} {𝓡𝓟 : RoutingProblem 𝓡𝓐 n-1}
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  (X : RoutingProblem.RMatrix 𝓡𝓟)
  (j : Fin (suc n-1))
  (t : ℕ)
  {F : Subset (suc n-1)}
  (F-nonFull : Nonfull F)
  (F-nonEmpty : Nonempty F)
  (F-fixed : ∀ {i} → i ∈ F → i ∈ᵤ NodeSets.Fixed 𝓟𝓢𝓒 X j t)
  where

  open Prelude 𝓟𝓢𝓒
  open Extrema ≤₊-totalOrder

  weightₑ : 𝕋 → Edge → Route
  weightₑ t (i , k) = A i k ▷ σ^ t X k j

  abstract
  
    e↷F⇒w[t+s]≡w[t] : ∀ {e} → e ↷ F → ∀ s → weightₑ (t + s) e ≈ weightₑ t e
    e↷F⇒w[t+s]≡w[t] (_ , k∈F) s = ▷-cong (A _ _) (proj₁ (F-fixed k∈F) s)
    
    -- At least one edge out of the fixed subtree exists
  
    eₐ : Edge
    eₐ = (proj₁ F-nonFull , proj₁ F-nonEmpty)

    eₐ↷F : eₐ ↷ F
    eₐ↷F = (proj₂ F-nonFull , proj₂ F-nonEmpty)
  
    -- Find the minimum edge out of the fixed subtree
  
    eₘᵢₙ : Edge
    eₘᵢₙ = argmin (weightₑ t) eₐ (cutset F)
      
  iₘᵢₙ : Node
  iₘᵢₙ = proj₁ eₘᵢₙ
    
  kₘᵢₙ : Node
  kₘᵢₙ = proj₂ eₘᵢₙ

  abstract
  
    -- Properties of the edge

    eₘᵢₙ↷F : eₘᵢₙ ↷ F
    eₘᵢₙ↷F = argmin-all eₐ↷F (∈cutset⇒↷ F)
  
    iₘᵢₙ∉F : iₘᵢₙ ∉ F
    iₘᵢₙ∉F = proj₁ eₘᵢₙ↷F

    kₘᵢₙ∈F : kₘᵢₙ ∈ F
    kₘᵢₙ∈F = proj₂ eₘᵢₙ↷F
    
    eₘᵢₙ-isMinₜ : ∀ {e} → e ↷ F → weightₑ t eₘᵢₙ ≤₊ weightₑ t e
    eₘᵢₙ-isMinₜ e↷F = lookup (f[argmin]≤f[xs] eₐ (cutset F)) (↷⇒∈cutset e↷F)

    eₘᵢₙ-isMinₜ₊ₛ : ∀ {e} → e ↷ F → ∀ s →
                    weightₑ (t + s) eₘᵢₙ ≤₊ weightₑ (t + s) e
    eₘᵢₙ-isMinₜ₊ₛ {e} e↷F s = begin
      weightₑ (t + s) eₘᵢₙ  ≈⟨ e↷F⇒w[t+s]≡w[t] eₘᵢₙ↷F s ⟩
      weightₑ t       eₘᵢₙ  ≤⟨ eₘᵢₙ-isMinₜ e↷F ⟩
      weightₑ t       e     ≈⟨ ≈-sym (e↷F⇒w[t+s]≡w[t] e↷F s) ⟩
      weightₑ (t + s) e     ∎
      where open PartialOrderReasoning ≤₊-poset
