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
open import RoutingLib.Data.Fin.Subset using (Nonfull)
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
import RoutingLib.Routing.BellmanFord.PathVector.ConvergenceTime.EdgeSets as EdgeSets
import RoutingLib.Routing.BellmanFord.PathVector.ConvergenceTime.FixedSubtree as FixedSubtree
import RoutingLib.Routing.BellmanFord.Properties as P

module RoutingLib.Routing.BellmanFord.PathVector.ConvergenceTime.Proof
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
  open FixedSubtree 𝓟𝓢𝓒 X j t-1 j∈F F-nonfull F-fixed
  open EdgeSets 𝓟𝓢𝓒 X j t-1 j∈F F-nonfull F-fixed
  
  --------------------------------------------------------------------------
  -- Some lemmas

  private

    t : ℕ
    t = suc t-1
    
    lemma₃ : ∀ s {e} → eₘᵢₙ ≤[ t + (n-1 + s) ] e → eₘᵢₙ ≤[ t + n-1 + s ] e
    lemma₃ s {e} eₘᵢₙ≤e = subst (eₘᵢₙ ≤[_] e) (sym (+-assoc t n-1 s)) eₘᵢₙ≤e

    
      
  ------------------------------------------------------------------------
  -- Therefore at time (t + n ∸ | F |) there is no more dangerous junk

  -- postulate junk-expiry : 

  iₘᵢₙ-pred≤ : ∀ s → A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + n-1 + s) X kₘᵢₙ j ≤₊ σ^ (suc (t + n-1 + s)) X iₘᵢₙ j
  iₘᵢₙ-pred≤ s with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ (σ^ (t + n-1 + s) X) iₘᵢₙ j
  ... | inj₂ σXᵢⱼ≈Iᵢⱼ    = begin
    A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + n-1 + s) X kₘᵢₙ j ≤⟨ ⊕-identityˡ _ ⟩
    0#                                     ≈⟨ ≈-reflexive (sym (Iᵢⱼ≡0# j≢iₘᵢₙ)) ⟩
    I iₘᵢₙ j                               ≈⟨ ≈-sym σXᵢⱼ≈Iᵢⱼ ⟩
    σ^ (suc (t + n-1 + s)) X iₘᵢₙ j        ∎
    where open POR ≤₊-poset
  ... | inj₁ (k , σXᵢⱼ≈AᵢₖXₖⱼ) with eₘᵢₙ ≤[ t + (n-1 + s) ]? (iₘᵢₙ , k)
  ...   | yes eₘᵢₙ≤e = begin
    A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + n-1 + s)   X kₘᵢₙ j ≤⟨ lemma₃ s eₘᵢₙ≤e ⟩
    A iₘᵢₙ k    ▷ σ^ (t + n-1 + s)   X k   j ≈⟨ ≈-sym σXᵢⱼ≈AᵢₖXₖⱼ ⟩
    σ^ (suc (t + n-1 + s)) X iₘᵢₙ j          ∎
    where open POR ≤₊-poset
  ...   | no  eₘᵢₙ≰e with k ∈? F | Real? (t + (n-1 + s)) k
  ...     | yes  k∈F | _       = contradiction (eₘᵢₙ-isMinₜ₊ₛ (iₘᵢₙ∉F , k∈F) (n-1 + s)) eₘᵢₙ≰e
  ...     | no   k∉F | yes k∈R = contradiction (∈Real (n-1 + s) iₘᵢₙ k∈R k∉F ≈ₚ-refl) eₘᵢₙ≰e
  ...     | no   k∉F | no  k∉R = contradiction
    (junk-length (n-1 + s) (k∉R , ≰₊⇒>₊ eₘᵢₙ≰e))
    (<⇒≱ (<-transˡ (lengthₑ<n (t + (n-1 + s)) (iₘᵢₙ , k)) (m≤m+n n s)))

  iₘᵢₙ-pred : ∀ s → σ^ (t + n + s) X iₘᵢₙ j ≈ A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + (n-1 + s)) X kₘᵢₙ j
  iₘᵢₙ-pred s = begin
    σ^ (t + n + s) X iₘᵢₙ j                  ≡⟨ cong (λ v → σ^ (v + s) X iₘᵢₙ j) (+-suc t n-1) ⟩
    σ^ (suc t + n-1 + s) X iₘᵢₙ j            ≈⟨ ≤₊-antisym (σXᵢⱼ≤Aᵢₖ▷Xₖⱼ
                                                (σ^ (t + n-1 + s) X) iₘᵢₙ j kₘᵢₙ) (iₘᵢₙ-pred≤ s) ⟩
    A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + n-1 + s) X kₘᵢₙ j   ≡⟨ cong (λ v → A iₘᵢₙ kₘᵢₙ ▷ σ^ v X kₘᵢₙ j) (+-assoc t n-1 s) ⟩
    A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + (n-1 + s)) X kₘᵢₙ j ∎
    where open EqReasoning S
    

  private

    lemma₄ : ∀ {p} → path (σ^ (t + n) X iₘᵢₙ j) ≡ p →
             path (A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + n-1) X kₘᵢₙ j) ≈ₚ p
    lemma₄ {p} eq = begin
      path (A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + n-1)     X kₘᵢₙ j)   ≡⟨ cong (λ v → path (A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + v) X kₘᵢₙ j)) (sym (+-identityʳ n-1)) ⟩
      path (A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + (n-1 + 0)) X kₘᵢₙ j) ≈⟨ path-cong (≈-sym (iₘᵢₙ-pred 0)) ⟩
      path (σ^ (t + n + 0) X iₘᵢₙ j)                   ≡⟨ cong (λ v → path (σ^ v X iₘᵢₙ j)) (+-identityʳ (t + n)) ⟩
      path (σ^ (t + n) X iₘᵢₙ j)                       ≡⟨ eq ⟩
      p                                                ∎
      where open EqReasoning (ℙₛ n)


  iₘᵢₙ-settled : iₘᵢₙ ∈ᵤ Settled (t + n)
  iₘᵢₙ-settled s = begin
    σ^ (t + n + s) X iₘᵢₙ j                    ≈⟨ iₘᵢₙ-pred s ⟩
    A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + (n-1 + s)) X kₘᵢₙ j  ≈⟨ ▷-cong (A iₘᵢₙ kₘᵢₙ)
                                                  (Fixed-eq t kₘᵢₙ (n-1 + s) (n-1 + 0) kₘᵢₙ∈Fₜ) ⟩
    A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + (n-1 + 0)) X kₘᵢₙ j  ≈⟨ ≈-sym (iₘᵢₙ-pred 0) ⟩
    σ^ (t + n + 0) X iₘᵢₙ j                   ≡⟨ cong (λ v → σ^ v X iₘᵢₙ j) (+-identityʳ (t + n)) ⟩
    σ^ (t + n)     X iₘᵢₙ j                   ∎
    where open EqReasoning S

  iₘᵢₙ-pathSettled : Allₙ (Settled (t + n)) (path (σ^ (t + n) X iₘᵢₙ j))
  iₘᵢₙ-pathSettled with path (σ^ (t + n) X iₘᵢₙ j) | inspect path (σ^ (t + n) X iₘᵢₙ j)
  ... | invalid  | _ = invalid
  ... | valid [] | _ = valid []
  ... | valid ((_ , _) ∷ p ∣ _ ∣ _) | [ p[σᵗ⁺ⁿ]≡iₘk∷p ]
    with alignPathExtension (σ^ (t + n-1) X) iₘᵢₙ j kₘᵢₙ (lemma₄ p[σᵗ⁺ⁿ]≡iₘk∷p)
  ...   | refl , refl , p[σᵗ⁺ⁿ⁻¹Xₖⱼ]≈p with Fixedₜ⊆Fixedₜ₊ₛ t n kₘᵢₙ∈Fₜ
  ...     | (k∈S , pₖ∈S) with Allₙ-resp-≈ₚ pₖ∈S (≈ₚ-trans (path-cong (Fixed-eq t _ n n-1 kₘᵢₙ∈Fₜ)) p[σᵗ⁺ⁿ⁻¹Xₖⱼ]≈p)
  ...       | valid p∈S = valid ([ iₘᵢₙ-settled , k∈S ]∷ p∈S)

  iₘᵢₙ-fixed : iₘᵢₙ ∈ᵤ Fixed (t + n)
  iₘᵢₙ-fixed = iₘᵢₙ-settled , iₘᵢₙ-pathSettled
