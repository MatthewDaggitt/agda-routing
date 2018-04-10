open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _∸_; _<_; _≤_)
open import Data.Nat.Properties using (+-identityʳ; +-comm; +-suc; +-assoc; ≤-reflexive; <⇒≱; <-transˡ; m≤m+n)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Subset using (Subset; _∈_; _∉_; _∪_)
open import Data.Fin.Dec using (_∈?_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (_,_; _×_; ∃; ∃₂; proj₁; proj₂)
open import Data.List using (List; filter; allFin)
open import Data.List.All as All using (All; lookup)
open import Data.List.All.Properties using (filter⁺₁)
open import Data.List.Any using (Any)
open import Data.List.Any.Membership.Propositional
  using (_⊆_; lose) renaming (_∈_ to _∈ₘ_)
open import Function using (_∘_)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Unary
  using (∁; ∁?;  U; Decidable) renaming (_∈_ to _∈ᵤ_; _∉_ to _∉ᵤ_; _⊆_ to _⊆ᵤ_)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; cong; subst; refl; sym; trans; inspect; [_]; module ≡-Reasoning)
import Relation.Binary.PartialOrderReasoning as POR
import Relation.Binary.EqReasoning as EqReasoning

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
open import RoutingLib.Data.List.Extrema.Nat
open import RoutingLib.Relation.Unary using (_∩?_)
open import RoutingLib.Data.List using (allFinPairs)
open import RoutingLib.Data.List.Membership.Propositional.Properties using (∈-filter⁺; ∈-allFinPairs⁺)
open import RoutingLib.Function.Reasoning
import RoutingLib.Relation.Binary.Reasoning.StrictPartialOrder as SPOR

open import RoutingLib.Routing.Definitions
open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions
import RoutingLib.Routing.BellmanFord.PathVector.ConvergenceTime.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.PathVector.ConvergenceTime.NodeSets as NodeSets
import RoutingLib.Routing.BellmanFord.PathVector.ConvergenceTime.FixedSubtree as FixedSubtree
import RoutingLib.Routing.BellmanFord.Properties as P

module RoutingLib.Routing.BellmanFord.PathVector.ConvergenceTime.EdgeSets
  {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  {n-1} {𝓡𝓟 : RoutingProblem 𝓡𝓐 n-1}
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  (X : RoutingProblem.RMatrix 𝓡𝓟)
  (j : Fin (suc n-1))
  (t-1 : ℕ)
  {F : Subset (suc n-1)}
  (j∈F : j ∈ F)
  (F-nonfull : Nonfull F)
  (F-fixed : ∀ {i} → i ∈ F → i ∈ᵤ NodeSets.Fixed 𝓟𝓢𝓒 X j (suc t-1))
  where
  
  open Prelude 𝓟𝓢𝓒
  open Notation X j
  open NodeSets 𝓟𝓢𝓒 X j
  
  ----------------------------------------------------------------------------
  -- Inductive proof

  private
  
    t : ℕ
    t = suc t-1

  ¬Real⇒∉F : ∀ {s k} → k ∉ᵤ Real (t + s) → k ∉ F
  ¬Real⇒∉F {s} {k} k∉Realₜ₊ₛ k∈F =
       k∈F                         ∶ k ∈ F
    ∣> F-fixed                     ∶ k ∈ᵤ Fixed t
    ∣> Fixedₜ⊆Fixedₜ₊ₛ t s        ∶ k ∈ᵤ Fixed (t + s)
    ∣> Fixed⊆Real (t + s) ≈ₚ-refl ∶ k ∈ᵤ Real (t + s)
    ∣> k∉Realₜ₊ₛ                  ∶ ⊥


  --------------------------------------------------------------------------
  -- Compute the minimum cut edge (iₘᵢₙ , kₘᵢₙ) of F

  open FixedSubtree 𝓟𝓢𝓒 X j t-1 j∈F F-nonfull F-fixed

  --------------------------------------------------------------------------
  -- Some lemmas

  private

    lemma₂ : ∀ {s i k l} → σ^ (suc t + s) X k j ≈ A k l ▷ (σ^ (t + s) X l j) →
             eₘᵢₙ ≤[ t + s ] (k , l) → eₘᵢₙ ≤[ t + suc s ] (i , k)
    lemma₂ {s} {i} {k} {l} σ¹⁺ᵗ⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ eₘᵢₙ≤kl = (begin
      A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + suc s) X kₘᵢₙ j ≈⟨ ▷-cong (A iₘᵢₙ kₘᵢₙ)
                                               (Fixed-eq t kₘᵢₙ (suc s) s kₘᵢₙ∈Fₜ) ⟩
      A iₘᵢₙ kₘᵢₙ ▷ σ^ (t +     s) X kₘᵢₙ j ≤⟨ eₘᵢₙ≤kl ⟩
      A k l ▷ σ^ (t + s) X l j             ≤⟨ ⊕-absorbs-▷ (A i k) (A k l ▷ σ^ (t + s) X l j) ⟩
      A i k ▷ (A k l ▷ σ^ (t + s) X l j)   ≈⟨ ▷-cong (A i k) (≈-sym σ¹⁺ᵗ⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ) ⟩
      A i    k   ▷ σ^ (suc t + s) X k   j  ≈⟨ ≈-reflexive (cong (λ v → A i k ▷ σ^ v X k j)
                                               (sym (+-suc t s))) ⟩
      A i    k   ▷ σ^ (t + suc s) X k   j  ∎)
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
        A k l ▷ σ^ (t + s) X l j             ≤⟨ ⊕-absorbs-▷ (A i k) _ ⟩<
        A i k ▷ (A k l ▷ σ^ (t + s) X l j)   ≈⟨ ▷-cong _ (≈-sym σ¹⁺ᵗ⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ) ⟩<
        A i    k    ▷ σ^ (suc t + s) X k   j ≡⟨ cong (λ v → A i k ▷ σ^ v X k j) (sym (+-suc t s)) ⟩<
        A i    k    ▷ σ^ (t + suc s) X k   j <⟨ ik∈D₁₊ₛ ⟩≤
        A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + suc s) X kₘᵢₙ j ≈⟨ ▷-cong _ (Fixed-eq t kₘᵢₙ (suc s) s kₘᵢₙ∈Fₜ) ⟩≤
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

  DangerousJunk : 𝕋 → Edge → Set ℓ
  DangerousJunk s (i , k) = k ∉ᵤ Real (t + s) × (i , k) ∈ᵤ Dangerous s

  abstract
  
    DangerousJunk? : ∀ s → Decidable (DangerousJunk s)
    DangerousJunk? s (i , k) = (∁? (Real? (t + s)) k) ×-dec (Dangerous? s (i , k))

    DangerousJunk-extension : ∀ {s i k} → (i , k) ∈ᵤ DangerousJunk (suc s) →
                              ∃ λ l → (k , l) ∈ᵤ DangerousJunk s
                                × lengthₑ (t + suc s) (i , k) ≡ suc (lengthₑ (t + s) (k , l))
    DangerousJunk-extension {s} {i} {k} (k∉Rₜ₊₁₊ₛ , k∈Dₜ₊₁₊ₛ)
      with ¬Real-extension (t + s) k (¬Real-cong k∉Rₜ₊₁₊ₛ (+-suc t s))
    ... | (l , p , _ , _ , p[σ¹⁺ᵗ⁺ˢ]≈kl∷p , σ¹⁺ᵗ⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢ , p[σᵗ⁺ˢXₗⱼ]≈p) = 
      l , (
      Dangerous-predNotReal (¬Real⇒∉F k∉Rₜ₊₁₊ₛ) σ¹⁺ᵗ⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢ k∈Dₜ₊₁₊ₛ ,
      Dangerous-retraction σ¹⁺ᵗ⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢ k∈Dₜ₊₁₊ₛ) ,
      trans (cong (λ v → lengthₑ v (i , k)) (+-suc t s))
            (lengthₑ-extension i {t + s} {k} p[σ¹⁺ᵗ⁺ˢ]≈kl∷p p[σᵗ⁺ˢXₗⱼ]≈p)

  junk-length : ∀ s {e} → e ∈ᵤ DangerousJunk s → s < lengthₑ (t + s) e
  junk-length zero    {i , k} (k∉Rₜ₊ₛ , _) = ¬Real-length (t + zero) k k∉Rₜ₊ₛ
  junk-length (suc s) {i , k} ik∈Dₛ with DangerousJunk-extension ik∈Dₛ
  ... | (l , kl∈Jₛ , |ik|≡1+|kl|) = begin
    suc s                          <⟨ s≤s (junk-length s kl∈Jₛ) ⟩
    suc (lengthₑ (t + s) (k , l))  ≡⟨ sym |ik|≡1+|kl| ⟩
    lengthₑ (t + suc s) (i , k)    ∎
    where open ≤-Reasoning








  {-
  -------------------------------------------------------------------------
  -- We can enumerate all the dangerous junk at time (t + s)

  allJunk : 𝕋 → List Edge
  allJunk s = filter (DangerousJunk? s) (allFinPairs n)

  abstract

    allJunk-junk : ∀ s → All (DangerousJunk s) (allJunk s)
    allJunk-junk s = filter⁺₁ (DangerousJunk? s) (allFinPairs n)

    allJunk-complete : ∀ {s i} → i ∈ᵤ DangerousJunk s → i ∈ₘ allJunk s
    allJunk-complete i∈Jₛ = ∈-filter⁺ (DangerousJunk? _) i∈Jₛ (∈-allFinPairs⁺ _ _)

    allJunk-extension : ∀ {t e₁} → e₁ ∈ᵤ DangerousJunk (suc t) →
                        Any (λ e₂ → lengthₑ t e₂ < lengthₑ (suc t) e₁) (allJunk t)
    allJunk-extension k∈J₁₊ₜ with DangerousJunk-extension k∈J₁₊ₜ
    ... | (l , l∈Jₜ , |k|≡1+|l|) =
      lose (allJunk-complete l∈Jₜ) (≤-reflexive (sym |k|≡1+|l|))

  -------------------------------------------------------------------------
  -- We can also therefore calculate the dangerous junk with the shortest
  -- length. The length of the shortest dangerous junk increases every
  -- iteration.

  module _ where

    abstract

      smallestJunk : ∀ s → ∃ (DangerousJunk s) → Edge
      smallestJunk s (e , _) = argmin (lengthₑ s) e (allJunk s)

      smallestJunk-incr : ∀ s ∃s ∃s+1 →
                          lengthₑ s       (smallestJunk s ∃s) <
                          lengthₑ (suc s) (smallestJunk (suc s) ∃s+1)
      smallestJunk-incr s (e₁ , _) (e₂ , l∈J₁₊ₛ) =
        argmin[xs]<argmin[ys] e₁ (allJunk s)
          (inj₂ (allJunk-extension l∈J₁₊ₛ))
          (All.map (inj₂ ∘ allJunk-extension) (allJunk-junk (suc s)))

      smallestJunk-junk : ∀ s ∃s → smallestJunk s ∃s ∈ᵤ DangerousJunk s
      smallestJunk-junk s ∃s = argmin-all (lengthₑ s) (proj₂ ∃s) (allJunk-junk s)

      smallestJunk-smallest : ∀ s e ∃s → e ∈ᵤ DangerousJunk s →
                              lengthₑ s (smallestJunk s ∃s) ≤ lengthₑ s e
      smallestJunk-smallest s e (d , d∈Jₛ) e∈Jₛ =
        lookup (f[argmin]≤f[xs] d (allJunk s)) (allJunk-complete e∈Jₛ) 

  smallestJunk-length : ∀ s ∃s → s < lengthₑ s (smallestJunk s ∃s)
  smallestJunk-length zero    ∃s = DangerousJunk-length (smallestJunk-junk _ ∃s)
  smallestJunk-length (suc s) ∃s
    with DangerousJunk-extension (smallestJunk-junk (suc s) ∃s)
  ... | (l , kl∈Jₛ , |ik|≡1+|kl|) = begin
    suc s                                                 <⟨ s≤s (smallestJunk-length s (_ , kl∈Jₛ)) ⟩
    suc (lengthₑ s (smallestJunk s (_ , kl∈Jₛ)))          ≤⟨ s≤s (smallestJunk-smallest s _ _ kl∈Jₛ) ⟩
    suc (lengthₑ s (proj₂ (smallestJunk (suc s) ∃s) , l)) ≡⟨ sym |ik|≡1+|kl| ⟩
    lengthₑ (suc s) (smallestJunk (suc s) ∃s)             ∎
    where open ≤-Reasoning
  -}
