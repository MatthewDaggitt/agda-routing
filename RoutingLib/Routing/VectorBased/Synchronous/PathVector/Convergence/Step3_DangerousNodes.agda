open import Data.Nat using (ℕ; NonZero; zero; suc; z≤n; s≤s; _+_; _<_; _≤_)
open import Data.Nat.Properties using (<⇒≱; +-suc; m≤m+n; <-≤-trans; module ≤-Reasoning)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (any?)
open import Data.Fin.Subset using (Subset; _∈_; _∉_; _∪_)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Product using (_,_; _×_; ∃; ∃₂; proj₁; proj₂)
open import Data.List.Membership.Propositional.Properties using (∈-filter⁺)
open import Data.List.Relation.Unary.All using (lookup)
open import Function using (_∘_)
open import Relation.Nullary using (Dec; ¬_; yes; no; _×-dec_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary
  using (Empty; Decidable) renaming (_∈_ to _∈ᵤ_; _∉_ to _∉ᵤ_; _⊆_ to _⊆ᵤ_)
open import Relation.Unary.Properties using (∁?; _∩?_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; cong; subst; refl; sym; trans; inspect; [_]; module ≡-Reasoning)
import Relation.Binary.Reasoning.PartialOrder as POR
import Data.List.Extrema as Extrema

open import RoutingLib.Data.Matrix using (SquareMatrix)
open import RoutingLib.Routing.Basics.Path.CertifiedI.AllVertices
open import RoutingLib.Routing.Basics.Path.CertifiedI.Properties
open import RoutingLib.Data.Fin.Subset
open import RoutingLib.Data.Fin.Subset.Cutset
open import RoutingLib.Data.List using (allFinPairs)
open import RoutingLib.Data.List.Membership.Propositional.Properties using (∈-allFinPairs⁺)
import RoutingLib.Function.Reasoning as FunctionalReasoning
open import RoutingLib.Data.Nat.Properties

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Prelude using (RoutingMatrix; AdjacencyMatrix)
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.Convergence.Prelude as Prelude
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.Convergence.Step1_NodeSets as Step1_NodeSets
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.Convergence.Step2_ConvergedSubtree as Step2_ConvergedSubtree

module RoutingLib.Routing.VectorBased.Synchronous.PathVector.Convergence.Step3_DangerousNodes
  {a b ℓ n-1} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (isPathAlgebra : IsCertifiedPathAlgebra algebra (suc n-1))
  (A : AdjacencyMatrix algebra (suc n-1))
  (X : RoutingMatrix   algebra (suc n-1))
  (j : Fin (suc n-1))
  (open Prelude isRoutingAlgebra isPathAlgebra A)
  (open Step1_NodeSets isRoutingAlgebra isPathAlgebra A X j)
  (isIncreasing  : IsIncreasing algebra)
  (t : ℕ)
  (C : Subset n)
  (C-nonFull : Nonfull C)
  (j∈C : j ∈ C)
  (C⊆𝓒ₜ : ∀ {i} → i ∈ C → i ∈ᵤ 𝓒 t)
  where

open Notation X j
open Extrema ≤₊-totalOrder

--------------------------------------------------------------------------
-- Compute the minimum cut edge (iₘᵢₙ , kₘᵢₙ) of C

open Step2_ConvergedSubtree isRoutingAlgebra isPathAlgebra A X j t C C-nonFull j∈C
  
------------------------------------------------------------------------------
-- More complex properties of eₘᵢₙ

kₘᵢₙ∈𝓒ₜ : kₘᵢₙ ∈ᵤ 𝓒 t
kₘᵢₙ∈𝓒ₜ = C⊆𝓒ₜ kₘᵢₙ∈C

-- The weight of any edge that cuts the provably converged set is
-- always constant after time t.
e↷C⇒w[t+s]≡w[t] : ∀ {e} → e ↷ C →
                  ∀ s → weightₑ (t + s) e ≈ weightₑ t e
e↷C⇒w[t+s]≡w[t] (_ , k∈C) s = ▷-cong (A _ _) (proj₁ (C⊆𝓒ₜ k∈C) s)

-- The weight of any edge that cuts the provably converged set is
-- always greater than the minimum edge after time t.
c↷C⇒eₘᵢₙ≤e : ∀ {e} → e ↷ C →
             ∀ s → weightₑ (t + s) eₘᵢₙ ≤₊ weightₑ (t + s) e
c↷C⇒eₘᵢₙ≤e {e} e↷C s = begin
  weightₑ (t + s) eₘᵢₙ  ≈⟨  e↷C⇒w[t+s]≡w[t] eₘᵢₙ↷C s ⟩
  weightₑ t       eₘᵢₙ  ≤⟨ c↷C⇒eₘᵢₙ≤ₜe e↷C ⟩
  weightₑ t       e     ≈˘⟨ e↷C⇒w[t+s]≡w[t] e↷C s ⟩
  weightₑ (t + s) e     ∎
  where open POR ≤₊-poset

-- If a node's path is invalid, then the weight of any edge from
-- that node is always greater than the minimum edge. 
invalid⇒eₘᵢₙ≤e : ∀ s {i k} →
                 path (σ (t + s) X k j) ≈ₚ invalid →
                 eₘᵢₙ ≤[ t + s ] (i , k)
invalid⇒eₘᵢₙ≤e s {i} {k} p[σᵗ⁺ˢXₖⱼ]≈∅ = begin
  A iₘᵢₙ kₘᵢₙ ▷ σ (t + s) X kₘᵢₙ j ≤⟨ ≤₊-maximum _ ⟩
  ∞#                               ≈˘⟨ ▷-fixedPoint (A i k) ⟩
  A i    k    ▷ ∞#                 ≈˘⟨ ▷-cong (A i k) (path[r]≈∅⇒r≈∞ p[σᵗ⁺ˢXₖⱼ]≈∅) ⟩
  A i    k    ▷ σ (t + s) X k j    ∎
  where open POR ≤₊-poset

-- If a node's path is trival, then the weight of any edge from
-- that node is always greater than the minimum edge. 
trivial⇒eₘᵢₙ≤e : ∀ s {i k} → .{{NonZero (t + s)}} → k ∉ C → 
                 path (σ (t + s) X k j) ≈ₚ trivial →
                 eₘᵢₙ ≤[ t + s ] (i , k)
trivial⇒eₘᵢₙ≤e s {i} {k} k∉C p[σᵗ⁺ˢXₖⱼ]≈[]
  rewrite p[σᵗXᵢⱼ]≈[]⇒i≡j X (t + s) k j p[σᵗ⁺ˢXₖⱼ]≈[] = contradiction j∈C k∉C

∉𝓡⇒∉C : ∀ {s k} → k ∉ᵤ 𝓡 (t + s) → k ∉ C
∉𝓡⇒∉C {s} {k} k∉𝓡ₜ₊ₛ k∈C = begin⟨ k∈C ⟩
  ∴ k ∈ C            $⟨ C⊆𝓒ₜ ⟩ 
  ∴ k ∈ᵤ 𝓒 t         $⟨ 𝓒ₜ⊆𝓒ₜ₊ₛ t s ⟩
  ∴ k ∈ᵤ 𝓒 (t + s)   $⟨ 𝓒ₜ⊆𝓡ₜ (t + s) ≈ₚ-refl ⟩
  ∴ k ∈ᵤ 𝓡 (t + s)   $⟨ k∉𝓡ₜ₊ₛ ⟩
  ∴ ⊥                 ∎
  where open FunctionalReasoning

safe-extension : ∀ {s r i k l} →
                 σ (t + r) X k j ≈ A k l ▷ (σ (t + s) X l j) →
                 eₘᵢₙ ≤[ t + s ] (k , l) →
                 eₘᵢₙ ≤[ t + r ] (i , k)
safe-extension {s} {r} {i} {k} {l} σ¹⁺ᵗ⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ eₘᵢₙ≤kl = begin
  A iₘᵢₙ kₘᵢₙ ▷ σ (t + r) X kₘᵢₙ j  ≈⟨ ▷-cong (A iₘᵢₙ kₘᵢₙ) (𝓒-eq t kₘᵢₙ r s kₘᵢₙ∈𝓒ₜ) ⟩
  A iₘᵢₙ kₘᵢₙ ▷ σ (t + s) X kₘᵢₙ j  ≤⟨ eₘᵢₙ≤kl ⟩
  A k l ▷ σ (t + s) X l j           ≤⟨ isIncreasing (A i k) (A k l ▷ σ (t + s) X l j) ⟩
  A i k ▷ (A k l ▷ σ (t + s) X l j) ≈˘⟨ ▷-cong (A i k) σ¹⁺ᵗ⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ ⟩
  A i k ▷ σ (t + r) X k   j         ∎
  where open POR ≤₊-poset

∈𝓡 : ∀ s i {k p} → .{{NonZero (t + s)}} →
     path (σ (t + s) X k j) ≈ₚ p →
     k ∈ᵤ 𝓡 (t + s) → k ∉ C → 
     eₘᵢₙ ≤[ t + s ] (i , k)
∈𝓡 s i {_} {invalid} p[σᵗ⁺ˢXₖⱼ]≈∅  _      _   = invalid⇒eₘᵢₙ≤e s p[σᵗ⁺ˢXₖⱼ]≈∅
∈𝓡 s i {_} {trivial} p[σᵗ⁺ˢXₖⱼ]≈[] k∈Rₛ₊ₜ k∉C = trivial⇒eₘᵢₙ≤e s k∉C p[σᵗ⁺ˢXₖⱼ]≈[]
∈𝓡 s i {_} {valid ((m , l) ∷ p ∣ _ ∣ _)} p[σᵗ⁺ˢXₖⱼ]≈kl∷p k∈Rₛ₊ₜ k∉C 
  with ∈𝓡 s m {_} {valid p} | 𝓡-path (t + s) p[σᵗ⁺ˢXₖⱼ]≈kl∷p k∈Rₛ₊ₜ
... | rec | valid ([ _ , l∈Rₛ₊ₜ ]∷ _)
    with 𝓡-alignment (t + s) k∈Rₛ₊ₜ p[σᵗ⁺ˢXₖⱼ]≈kl∷p
...   | refl , (σᵗ⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢXₗⱼ , _) , p[σᵗ⁺ˢXₗⱼ]≈p with l ∈? C
...     | no  l∉C = safe-extension (≈-sym σᵗ⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢXₗⱼ) (rec p[σᵗ⁺ˢXₗⱼ]≈p l∈Rₛ₊ₜ l∉C )
...     | yes l∈C = safe-extension (≈-sym σᵗ⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢXₗⱼ) (c↷C⇒eₘᵢₙ≤e (k∉C , l∈C) s)

-------------------------------------------------------------------------
-- The only time that the source node of the minimal edge out of the fixed
-- tree will not become fixed itself is if there is some non-real routes
-- out there floating around that are falsely advertising a better route
-- than that of the minimal edge out of the fixed subtree.

-- Dangerous nodes are those who currently have a better route than the
-- minimal edge

Dangerous : 𝕋 → Edge → Set ℓ
Dangerous s e = e <[ t + s ] eₘᵢₙ

abstract

  Dangerous? : ∀ s → Decidable (Dangerous s)
  Dangerous? s e = e <[ t + s ]? eₘᵢₙ

  Dangerous-retraction : ∀ {i k l s} → σ (t + suc s) X k j ≈ A k l ▷ (σ (t + s) X l j) →
                         (i , k) ∈ᵤ Dangerous (suc s) → (k , l) ∈ᵤ Dangerous s
  Dangerous-retraction {i} {k} {l} {s} σ¹⁺ᵗ⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ ik∈D₁₊ₛ = begin-strict
    A k l ▷ σ (t + s) X l j              ≈˘⟨ σ¹⁺ᵗ⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ ⟩
    σ (t + suc s) X k j                  ≤⟨ isIncreasing (A i k) _ ⟩
    A i    k    ▷ σ (t + suc s) X k   j  <⟨ ik∈D₁₊ₛ ⟩
    A iₘᵢₙ kₘᵢₙ ▷ σ (t + suc s) X kₘᵢₙ j ≈⟨ ▷-cong _ (𝓒-eq t kₘᵢₙ (suc s) s kₘᵢₙ∈𝓒ₜ) ⟩
    A iₘᵢₙ kₘᵢₙ ▷ σ (t + s)     X kₘᵢₙ j ∎
    where open POR ≤₊-poset

  Dangerous-predNot𝓡 : ∀ {i k l s} → .{{NonZero (t + s)}} → k ∉ C →
                          σ (t + suc s) X k j ≈ A k l ▷ σ (t + s) X l j →
                          (i , k) ∈ᵤ Dangerous (suc s) → l ∉ᵤ 𝓡 (t + s)
  Dangerous-predNot𝓡 {i} {k} {l} {s} k∉C σᵗ⁺¹⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ ik∈D₁₊ₛ l∈Rₜ₊ₛ with l ∈? C
  ... | no  l∉C = <₊⇒≱₊ ik∈D₁₊ₛ (safe-extension σᵗ⁺¹⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ (∈𝓡 s k ≈ₚ-refl l∈Rₜ₊ₛ l∉C))
  ... | yes l∈C = <₊⇒≱₊ ik∈D₁₊ₛ (safe-extension σᵗ⁺¹⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ (c↷C⇒eₘᵢₙ≤e (k∉C , l∈C) s))

-------------------------------------------------------------------------
-- DangerousJunk nodes are those who are both dangerous and aren't
-- real, and therefore don't respect the minimal spanning tree
-- constraints.

𝓓 : 𝕋 → Node → Set ℓ
𝓓 s k = k ∉ᵤ 𝓡 (t + s) × ∃ λ i → (i , k) ∈ᵤ Dangerous s

abstract

  𝓓? : ∀ s → Decidable (𝓓 s)
  𝓓? s k = (∁? (𝓡? (t + s)) k) ×-dec (any? λ v → Dangerous? s (v , k))

  𝓓-retraction : ∀ {s k} → .{{NonZero (t + s)}} → k ∈ᵤ 𝓓 (suc s) →
                 ∃ λ l → l ∈ᵤ 𝓓 s × lengthₙ (suc t + s) k ≡ suc (lengthₙ(t + s) l)
  𝓓-retraction {s} {k} (k∉Rₜ₊₁₊ₛ , (i , k∈Dₜ₊₁₊ₛ))
    with ¬𝓡-retraction (t + s) k (¬𝓡-cong k∉Rₜ₊₁₊ₛ (+-suc t s))
  ... | (l , p , _ , _ , p[σ¹⁺ᵗ⁺ˢ]≈kl∷p , σ¹⁺ᵗ⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢ , p[σᵗ⁺ˢXₗⱼ]≈p) =
    l , l∈𝓓ₛ ,
    (lengthₙ-extension {t + s} {k} p[σ¹⁺ᵗ⁺ˢ]≈kl∷p p[σᵗ⁺ˢXₗⱼ]≈p)

    where

    σᵗ⁺¹⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢ : σ (t + suc s) X k j ≈ A k l ▷ σ (t + s) X l j
    σᵗ⁺¹⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢ = ≈-trans (≈-reflexive (cong (λ v → σ v X k j) (+-suc t s))) σ¹⁺ᵗ⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢ

    l∈𝓓ₛ : l ∈ᵤ 𝓓 s
    l∈𝓓ₛ = Dangerous-predNot𝓡 (∉𝓡⇒∉C k∉Rₜ₊₁₊ₛ) σᵗ⁺¹⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢ k∈Dₜ₊₁₊ₛ ,
            (k , Dangerous-retraction σᵗ⁺¹⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢ k∈Dₜ₊₁₊ₛ)

𝓓-length : ∀ s {i} → .{{NonZero t}} → i ∈ᵤ 𝓓 s → s < lengthₙ (t + s) i
𝓓-length zero    {i} (k∉Rₜ₊ₛ , _) = ∉𝓡⇒lengthOfPath>0 (t + zero) i k∉Rₜ₊ₛ
𝓓-length (suc s) {i} {{t≢0}} ik∈Dₛ with 𝓓-retraction {{+-presˡ-nonZero t s}} ik∈Dₛ
... | (l , l∈Jₛ , |i|≡1+|l|) = begin-strict
  suc s                    <⟨ s≤s (𝓓-length s l∈Jₛ) ⟩
  suc (lengthₙ (t + s) l)  ≡˘⟨ |i|≡1+|l| ⟩
  lengthₙ (suc t + s) i    ≡˘⟨ cong (λ v → lengthₙ v i) (+-suc t s) ⟩
  lengthₙ (t + suc s) i    ∎
  where open ≤-Reasoning

𝓓ₙ₋₁₊ₛ-empty : ∀ s → .{{NonZero t}} → Empty (𝓓 (n-1 + s))
𝓓ₙ₋₁₊ₛ-empty s k k∈𝓓ₙ₋₁ = contradiction
  (𝓓-length (n-1 + s) k∈𝓓ₙ₋₁)
  (<⇒≱ (<-≤-trans (lengthₑ<n (t + (n-1 + s)) (iₘᵢₙ , k)) (m≤m+n n s)))

eₘᵢₙ≤ₜ₊ₙ₋₁₊ₛe : .{{_ : NonZero t}} → ∀ s k → eₘᵢₙ ≤[ t + (n-1 + s) ] (iₘᵢₙ , k)
eₘᵢₙ≤ₜ₊ₙ₋₁₊ₛe s k with 𝓡? (t + (n-1 + s)) k | k ∈? C
... | _        | yes k∈C = c↷C⇒eₘᵢₙ≤e (iₘᵢₙ∉C , k∈C) (n-1 + s)
... | yes k∈𝓡 | no  k∉C = ∈𝓡 (n-1 + s) iₘᵢₙ {{+-presˡ-nonZero t (n-1 + s)}} ≈ₚ-refl k∈𝓡 k∉C
... | no  k∉𝓡 | no _     with eₘᵢₙ ≤[ t + (n-1 + s) ]? (iₘᵢₙ , k)
...   | yes eₘᵢₙ≤e = eₘᵢₙ≤e
...   | no  eₘᵢₙ≰e = contradiction (k∉𝓡 , iₘᵢₙ , ≰₊⇒>₊ eₘᵢₙ≰e) (𝓓ₙ₋₁₊ₛ-empty s k)
