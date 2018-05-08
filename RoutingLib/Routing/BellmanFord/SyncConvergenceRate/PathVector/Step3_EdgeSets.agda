open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _<_; _≤_)
open import Data.Nat.Properties using (+-suc)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; _∈_; _∉_; _∪_)
open import Data.Fin.Dec using (_∈?_)
open import Data.Product using (_,_; _×_; ∃; ∃₂)
open import Function using (_∘_)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Unary
  using (∁?; Decidable) renaming (_∈_ to _∈ᵤ_; _∉_ to _∉ᵤ_; _⊆_ to _⊆ᵤ_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; cong; subst; refl; sym; trans; inspect; [_]; module ≡-Reasoning)
import Relation.Binary.PartialOrderReasoning as POR

open import RoutingLib.Data.Matrix using (SquareMatrix)
open import RoutingLib.Data.SimplePath
  using (SimplePath; []; _∷_∣_∣_; invalid; valid; notThere; notHere; continue; length)
  renaming (_∈_ to _∈ₚ_)
open import RoutingLib.Data.SimplePath.Relation.Equality
open import RoutingLib.Data.SimplePath.Relation.Subpath
open import RoutingLib.Data.SimplePath.All
open import RoutingLib.Data.SimplePath.Properties
  using (∉-resp-≈ₚ; length-cong)
open import RoutingLib.Data.Fin.Subset using (Nonfull) renaming ()
open import RoutingLib.Data.Nat.Properties using (module ≤-Reasoning)
open import RoutingLib.Relation.Unary using (_∩?_)
open import RoutingLib.Data.Fin.Dec using (any?)
open import RoutingLib.Data.List using (allFinPairs)
open import RoutingLib.Data.List.Membership.Propositional.Properties using (∈-filter⁺; ∈-allFinPairs⁺)
open import RoutingLib.Function.Reasoning
import RoutingLib.Relation.Binary.Reasoning.StrictPartialOrder as SPOR

open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.BellmanFord.SyncConvergenceRate.PathVector.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.SyncConvergenceRate.PathVector.Step1_NodeSets as Step1_NodeSets
import RoutingLib.Routing.BellmanFord.SyncConvergenceRate.PathVector.Step2_ConvergedSubtree as Step2_ConvergedSubtree
open IncreasingPathAlgebra using (Route)

module RoutingLib.Routing.BellmanFord.SyncConvergenceRate.PathVector.Step3_EdgeSets
  {a b ℓ n-1} (algebra : IncreasingPathAlgebra a b ℓ (suc n-1))
  (X : SquareMatrix (Route algebra) (suc n-1))
  (j : Fin (suc n-1))
  (t-1 : ℕ)
  {F : Subset (suc n-1)}
  (j∈F : j ∈ F)
  (F-nonfull : Nonfull F)
  (F-fixed : ∀ {i} → i ∈ F → i ∈ᵤ Step1_NodeSets.Converged algebra X j (suc t-1))
  where
  
  open Prelude algebra
  open Notation X j
  open Step1_NodeSets algebra X j
  
  ----------------------------------------------------------------------------
  -- Inductive proof

  private
  
    t : ℕ
    t = suc t-1

  ¬Real⇒∉F : ∀ {s k} → k ∉ᵤ Real (t + s) → k ∉ F
  ¬Real⇒∉F {s} {k} k∉Realₜ₊ₛ k∈F =
       k∈F                         ∶ k ∈ F
    ∣> F-fixed                     ∶ k ∈ᵤ Converged t
    ∣> Convergedₜ⊆Convergedₜ₊ₛ t s        ∶ k ∈ᵤ Converged (t + s)
    ∣> Converged⊆Real (t + s) ≈ₚ-refl ∶ k ∈ᵤ Real (t + s)
    ∣> k∉Realₜ₊ₛ                  ∶ ⊥


  --------------------------------------------------------------------------
  -- Compute the minimum cut edge (iₘᵢₙ , kₘᵢₙ) of F

  open Step2_ConvergedSubtree algebra X j t-1 j∈F F-nonfull F-fixed

  --------------------------------------------------------------------------
  -- Some lemmas

  private

    lemma₂ : ∀ {s i k l} → σ^ (suc t + s) X k j ≈ A k l ▷ (σ^ (t + s) X l j) →
             eₘᵢₙ ≤[ t + s ] (k , l) → eₘᵢₙ ≤[ t + suc s ] (i , k)
    lemma₂ {s} {i} {k} {l} σ¹⁺ᵗ⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ eₘᵢₙ≤kl = (begin
      A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + suc s) X kₘᵢₙ j ≈⟨ ▷-cong (A iₘᵢₙ kₘᵢₙ)
                                               (Converged-eq t kₘᵢₙ (suc s) s kₘᵢₙ∈Fₜ) ⟩
      A iₘᵢₙ kₘᵢₙ ▷ σ^ (t +     s) X kₘᵢₙ j ≤⟨ eₘᵢₙ≤kl ⟩
      A k l ▷ σ^ (t + s) X l j              ≤⟨ ▷-increasing (A i k) (A k l ▷ σ^ (t + s) X l j) ⟩
      A i k ▷ (A k l ▷ σ^ (t + s) X l j)    ≈⟨ ▷-cong (A i k) (≈-sym σ¹⁺ᵗ⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ) ⟩
      A i    k   ▷ σ^ (suc t + s) X k   j   ≈⟨ ≈-reflexive (cong (λ v → A i k ▷ σ^ v X k j)
                                               (sym (+-suc t s))) ⟩
      A i    k   ▷ σ^ (t + suc s) X k   j   ∎)
      where open POR ≤₊-poset


  -------------------------------------------------------------------------
  -- The only time that the source node of the minimal edge out of the fixed
  -- tree will not become fixed itself is if there is some non-real routes
  -- out there floating around that are falsely advertising a better route
  -- than that of the minimal edge out of the fixed subtree.

  -- Dangerous nodes are those who currently have a better route than the
  -- minimal edge

  Dangerous : 𝕋 → Edge → Set ℓ
  Dangerous s e = e <[ t + s ] eₘᵢₙ

  module _ where

    abstract

      Dangerous? : ∀ s → Decidable (Dangerous s)
      Dangerous? s e = e <[ t + s ]? eₘᵢₙ

      Dangerous-retraction : ∀ {i k l s} → σ^ (suc t + s) X k j ≈ A k l ▷ (σ^ (t + s) X l j) →
                             (i , k) ∈ᵤ Dangerous (suc s) → (k , l) ∈ᵤ Dangerous s
      Dangerous-retraction {i} {k} {l} {s} σ¹⁺ᵗ⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ ik∈D₁₊ₛ = begin
        A k l ▷ σ^ (t + s) X l j              ≈⟨ ≈-sym σ¹⁺ᵗ⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ ⟩<
        σ^ (suc t + s) X k j                  ≤⟨ ▷-increasing (A i k) _ ⟩<
        A i    k    ▷ σ^ (suc t + s) X k   j  ≡⟨ cong (λ v → A i k ▷ σ^ v X k j) (sym (+-suc t s)) ⟩<
        A i    k    ▷ σ^ (t + suc s) X k   j  <⟨ ik∈D₁₊ₛ ⟩≤
        A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + suc s) X kₘᵢₙ j ≈⟨ ▷-cong _ (Converged-eq t kₘᵢₙ (suc s) s kₘᵢₙ∈Fₜ) ⟩≤
        A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + s)     X kₘᵢₙ j ∎
        where open SPOR ≤₊-poset

      Dangerous-predNotReal : ∀ {i k l s} → k ∉ F →
                              σ^ (suc t + s) X k j ≈ A k l ▷ (σ^ (t + s) X l j) →
                              (i , k) ∈ᵤ Dangerous (suc s) → l ∉ᵤ Real (t + s)
      Dangerous-predNotReal {i} {k} {l} {s} k∉F σ¹⁺ᵗ⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ ik∈D₁₊ₛ l∈Rₜ₊ₛ
        with l ∈? F | Dangerous-retraction σ¹⁺ᵗ⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ ik∈D₁₊ₛ
      ... | no  l∉F | l∈Dₛ = <₊⇒≱₊ ik∈D₁₊ₛ (lemma₂ σ¹⁺ᵗ⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ (∈Real s k l∈Rₜ₊ₛ l∉F ≈ₚ-refl ))
      ... | yes l∈F | l∈Dₛ = <₊⇒≱₊ ik∈D₁₊ₛ (lemma₂ σ¹⁺ᵗ⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ (eₘᵢₙ-isMinₜ₊ₛ (k∉F , l∈F) s))

  -------------------------------------------------------------------------
  -- DangerousJunk nodes are those who are both dangerous and aren't
  -- real, and therefore don't respect the minimal spanning tree
  -- constraints.

  DangerousJunk : 𝕋 → Node → Set ℓ
  DangerousJunk s k = k ∉ᵤ Real (t + s) × ∃ λ i → (i , k) ∈ᵤ Dangerous s

  abstract
  
    DangerousJunk? : ∀ s → Decidable (DangerousJunk s)
    DangerousJunk? s k = (∁? (Real? (t + s)) k) ×-dec (any? λ v → Dangerous? s (v , k))

    DangerousJunk-retraction : ∀ {s k} → k ∈ᵤ DangerousJunk (suc s) →
                               ∃ λ l → l ∈ᵤ DangerousJunk s
                                × lengthₙ (suc t + s) k ≡ suc (lengthₙ(t + s) l)
    DangerousJunk-retraction {s} {k} (k∉Rₜ₊₁₊ₛ , (i , k∈Dₜ₊₁₊ₛ))
      with ¬Real-retraction (t + s) k (¬Real-cong k∉Rₜ₊₁₊ₛ (+-suc t s))
    ... | (l , p , _ , _ , p[σ¹⁺ᵗ⁺ˢ]≈kl∷p , σ¹⁺ᵗ⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢ , p[σᵗ⁺ˢXₗⱼ]≈p) = 
      l ,
      l∈DJₛ ,
      (lengthₙ-extension {t + s} {k} p[σ¹⁺ᵗ⁺ˢ]≈kl∷p p[σᵗ⁺ˢXₗⱼ]≈p)

      where

      l∈DJₛ : l ∈ᵤ DangerousJunk s
      l∈DJₛ = Dangerous-predNotReal (¬Real⇒∉F k∉Rₜ₊₁₊ₛ) σ¹⁺ᵗ⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢ k∈Dₜ₊₁₊ₛ , (k , Dangerous-retraction σ¹⁺ᵗ⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢ k∈Dₜ₊₁₊ₛ)
      
      
  junk-length : ∀ s {i} → i ∈ᵤ DangerousJunk s → s < lengthₙ (t + s) i
  junk-length zero    {i} (k∉Rₜ₊ₛ , _) = ¬Real-length (t + zero) i k∉Rₜ₊ₛ
  junk-length (suc s) {i} ik∈Dₛ with DangerousJunk-retraction ik∈Dₛ
  ... | (l , l∈Jₛ , |i|≡1+|l|) = begin
    suc s                    <⟨ s≤s (junk-length s l∈Jₛ) ⟩
    suc (lengthₙ (t + s) l)  ≡⟨ sym |i|≡1+|l| ⟩
    lengthₙ (suc t + s) i    ≡⟨ sym (cong (λ v → lengthₙ v i) (+-suc t s)) ⟩
    lengthₙ (t + suc s) i    ∎
    where open ≤-Reasoning
