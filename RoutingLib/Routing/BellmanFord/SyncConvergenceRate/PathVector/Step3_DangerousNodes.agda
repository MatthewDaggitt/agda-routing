open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _<_; _≤_)
open import Data.Nat.Properties using (+-suc)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; _∈_; _∉_; _∪_)
open import Data.Fin.Dec using (_∈?_)
open import Data.Product using (_,_; _×_; ∃; ∃₂)
open import Data.List.Membership.Propositional.Properties using (∈-filter⁺)
open import Function using (_∘_)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Unary
  using (Decidable) renaming (_∈_ to _∈ᵤ_; _∉_ to _∉ᵤ_; _⊆_ to _⊆ᵤ_)
open import Relation.Unary.Properties using (∁?; _∩?_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; cong; subst; refl; sym; trans; inspect; [_]; module ≡-Reasoning)
import Relation.Binary.PartialOrderReasoning as POR
open import Function.Reasoning

open import RoutingLib.Data.Matrix using (SquareMatrix)
open import RoutingLib.Data.Path.Certified.FiniteEdge
  using (Path; []; _∷_∣_∣_; invalid; valid; notThere; notHere; continue; length)
  renaming (_∈_ to _∈ₚ_)
open import RoutingLib.Data.Path.Certified.FiniteEdge.All
open import RoutingLib.Data.Path.Certified.FiniteEdge.Properties
open import RoutingLib.Data.Fin.Subset using (Nonfull) renaming ()
open import RoutingLib.Data.Nat.Properties using (module ≤-Reasoning)
open import RoutingLib.Data.Fin.Dec using (any?)
open import RoutingLib.Data.List using (allFinPairs)
open import RoutingLib.Data.List.Membership.Propositional.Properties using (∈-allFinPairs⁺)
import RoutingLib.Relation.Binary.Reasoning.StrictPartialOrder as SPOR

open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.BellmanFord.SyncConvergenceRate.PathVector.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.SyncConvergenceRate.PathVector.Step1_NodeSets as Step1_NodeSets
import RoutingLib.Routing.BellmanFord.SyncConvergenceRate.PathVector.Step2_ConvergedSubtree as Step2_ConvergedSubtree
open IncreasingPathAlgebra using (Route)

module RoutingLib.Routing.BellmanFord.SyncConvergenceRate.PathVector.Step3_DangerousNodes
  {a b ℓ n-1} (algebra : IncreasingPathAlgebra a b ℓ (suc n-1))
  (X : SquareMatrix (Route algebra) (suc n-1))
  (j : Fin (suc n-1))
  (t-1 : ℕ)
  {C : Subset (suc n-1)}
  (j∈C : j ∈ C)
  (C-nonfull : Nonfull C)
  (C-fixed : ∀ {i} → i ∈ C → i ∈ᵤ Step1_NodeSets.𝓒 algebra X j (suc t-1))
  where

  open Prelude algebra
  open Notation X j
  open Step1_NodeSets algebra X j

  ----------------------------------------------------------------------------
  -- Inductive proof

  private

    t : ℕ
    t = suc t-1

  ¬𝓡⇒∉C : ∀ {s k} → k ∉ᵤ 𝓡 (t + s) → k ∉ C
  ¬𝓡⇒∉C {s} {k} k∉𝓡ₜ₊ₛ k∈C =
       k∈C                     ∶ k ∈ C
    |> C-fixed                 ∶ k ∈ᵤ 𝓒 t
    |> 𝓒ₜ⊆𝓒ₜ₊ₛ t s            ∶ k ∈ᵤ 𝓒 (t + s)
    |> 𝓒ₜ⊆𝓡ₜ (t + s) ≈ₚ-refl  ∶ k ∈ᵤ 𝓡 (t + s)
    |> k∉𝓡ₜ₊ₛ                 ∶ ⊥


  --------------------------------------------------------------------------
  -- Compute the minimum cut edge (iₘᵢₙ , kₘᵢₙ) of C

  open Step2_ConvergedSubtree algebra X j t-1 j∈C C-nonfull C-fixed

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

      Dangerous-retraction : ∀ {i k l s} → σ^ (t + suc s) X k j ≈ A k l ▷ (σ^ (t + s) X l j) →
                             (i , k) ∈ᵤ Dangerous (suc s) → (k , l) ∈ᵤ Dangerous s
      Dangerous-retraction {i} {k} {l} {s} σ¹⁺ᵗ⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ ik∈D₁₊ₛ = begin
        A k l ▷ σ^ (t + s) X l j              ≈⟨ ≈-sym σ¹⁺ᵗ⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ ⟩<
        σ^ (t + suc s) X k j                  ≤⟨ ▷-increasing (A i k) _ ⟩<
        A i    k    ▷ σ^ (t + suc s) X k   j  <⟨ ik∈D₁₊ₛ ⟩≤
        A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + suc s) X kₘᵢₙ j ≈⟨ ▷-cong _ (𝓒-eq t kₘᵢₙ (suc s) s kₘᵢₙ∈𝓒ₜ) ⟩≤
        A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + s)     X kₘᵢₙ j ∎
        where open SPOR ≤₊-poset

      Dangerous-predNot𝓡 : ∀ {i k l s} → k ∉ C →
                              σ^ (t + suc s) X k j ≈ A k l ▷ (σ^ (t + s) X l j) →
                              (i , k) ∈ᵤ Dangerous (suc s) → l ∉ᵤ 𝓡 (t + s)
      Dangerous-predNot𝓡 {i} {k} {l} {s} k∉C σᵗ⁺¹⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ ik∈D₁₊ₛ l∈Rₜ₊ₛ with l ∈? C
      ... | no  l∉C = <₊⇒≱₊ ik∈D₁₊ₛ (safe-extension σᵗ⁺¹⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ (∈𝓡 s k l∈Rₜ₊ₛ l∉C ≈ₚ-refl ))
      ... | yes l∈C = <₊⇒≱₊ ik∈D₁₊ₛ (safe-extension σᵗ⁺¹⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ (eₘᵢₙ-isMinₜ₊ₛ (k∉C , l∈C) s))

  -------------------------------------------------------------------------
  -- DangerousJunk nodes are those who are both dangerous and aren't
  -- real, and therefore don't respect the minimal spanning tree
  -- constraints.

  𝓓 : 𝕋 → Node → Set ℓ
  𝓓 s k = k ∉ᵤ 𝓡 (t + s) × ∃ λ i → (i , k) ∈ᵤ Dangerous s

  abstract

    𝓓? : ∀ s → Decidable (𝓓 s)
    𝓓? s k = (∁? (𝓡? (t + s)) k) ×-dec (any? λ v → Dangerous? s (v , k))




    𝓓-retraction : ∀ {s k} → k ∈ᵤ 𝓓 (suc s) →
                               ∃ λ l → l ∈ᵤ 𝓓 s
                                × lengthₙ (suc t + s) k ≡ suc (lengthₙ(t + s) l)
    𝓓-retraction {s} {k} (k∉Rₜ₊₁₊ₛ , (i , k∈Dₜ₊₁₊ₛ))
      with ¬𝓡-retraction (t + s) k (¬𝓡-cong k∉Rₜ₊₁₊ₛ (+-suc t s))
    ... | (l , p , _ , _ , p[σ¹⁺ᵗ⁺ˢ]≈kl∷p , σ¹⁺ᵗ⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢ , p[σᵗ⁺ˢXₗⱼ]≈p) =
      l , l∈𝓓ₛ ,
      (lengthₙ-extension {t + s} {k} p[σ¹⁺ᵗ⁺ˢ]≈kl∷p p[σᵗ⁺ˢXₗⱼ]≈p)

      where

      σᵗ⁺¹⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢ : σ^ (t + suc s) X k j ≈ A k l ▷ σ^ (t + s) X l j
      σᵗ⁺¹⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢ = ≈-trans (≈-reflexive (cong (λ v → σ^ v X k j) (+-suc t s))) σ¹⁺ᵗ⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢ

      l∈𝓓ₛ : l ∈ᵤ 𝓓 s
      l∈𝓓ₛ = Dangerous-predNot𝓡 (¬𝓡⇒∉C k∉Rₜ₊₁₊ₛ) σᵗ⁺¹⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢ k∈Dₜ₊₁₊ₛ ,
              (k , Dangerous-retraction σᵗ⁺¹⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢ k∈Dₜ₊₁₊ₛ)


  𝓓-length : ∀ s {i} → i ∈ᵤ 𝓓 s → s < lengthₙ (t + s) i
  𝓓-length zero    {i} (k∉Rₜ₊ₛ , _) = ¬𝓡-length (t + zero) i k∉Rₜ₊ₛ
  𝓓-length (suc s) {i} ik∈Dₛ with 𝓓-retraction ik∈Dₛ
  ... | (l , l∈Jₛ , |i|≡1+|l|) = begin
    suc s                    <⟨ s≤s (𝓓-length s l∈Jₛ) ⟩
    suc (lengthₙ (t + s) l)  ≡⟨ sym |i|≡1+|l| ⟩
    lengthₙ (suc t + s) i    ≡⟨ sym (cong (λ v → lengthₙ v i) (+-suc t s)) ⟩
    lengthₙ (t + suc s) i    ∎
    where open ≤-Reasoning
