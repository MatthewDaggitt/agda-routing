open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _∸_; _<_; _≤_)
open import Data.Nat.Properties using (+-identityʳ; +-comm; +-suc; +-assoc; ≤-reflexive)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Subset using (Subset; _∈_; _∉_; _∪_)
open import Data.Fin.Dec using (_∈?_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (_,_; _×_; ∃; ∃₂; proj₁; proj₂)
open import Data.List using (List; filter; allFin)
open import Data.List.All as All using (All)
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
  using (_≡_; cong; subst; refl; sym; trans; inspect; [_]; module ≡-Reasoning)
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
open import RoutingLib.Data.List.Extrema.Nat
open import RoutingLib.Relation.Unary using (_∩?_)
open import RoutingLib.Data.List using (allFinPairs)
open import RoutingLib.Data.List.Membership.Propositional.Properties using (∈-filter⁺; ∈-allFinPairs⁺)
open import RoutingLib.Function.Reasoning
import RoutingLib.Relation.Binary.Reasoning.StrictPartialOrder as SPOR

open import RoutingLib.Routing.Definitions
open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions
open import RoutingLib.Routing.BellmanFord.Properties using (Iᵢᵢ≡1#; Iᵢⱼ≡0#; Iᵢⱼ≈0⊎1)
import RoutingLib.Routing.BellmanFord.PathVector.ConvergenceTime.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.PathVector.ConvergenceTime.NodeSets as NodeSets
import RoutingLib.Routing.BellmanFord.PathVector.ConvergenceTime.FixedSubtree as FixedSubtree
import RoutingLib.Routing.BellmanFord.Properties as P

module RoutingLib.Routing.BellmanFord.PathVector.ConvergenceTime.Proof
  {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  {n-1} {𝓡𝓟 : RoutingProblem 𝓡𝓐 n-1}
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  where
  
  open Prelude 𝓟𝓢𝓒
  
  module _ (X : RMatrix) (j : Fin n) where

    open NodeSets 𝓟𝓢𝓒 X j
    
    ----------------------------------------------------------------------------
    -- Inductive proof

    module InductiveStep (t-1 : 𝕋) {F : Subset n}
             (F-fixed : ∀ {i} → i ∈ F → i ∈ᵤ Fixed (suc t-1))
             (F-nonfull : Nonfull F)
             (j∈F : j ∈ F)
             where

      t : ℕ
      t = suc t-1

      ¬Real⇒∉F : ∀ {s k} → k ∉ᵤ Real (t + s) → k ∉ F
      ¬Real⇒∉F {s} {k} k∉Realₜ₊ₛ k∈F =
           k∈F                         ∶ k ∈ F
        ∣> F-fixed                     ∶ k ∈ᵤ Fixed t
        ∣> Fixedₜ⊆Fixedₛ₊ₜ t s        ∶ k ∈ᵤ Fixed (t + s)
        ∣> Fixed⊆Real (t + s) ≈ₚ-refl ∶ k ∈ᵤ Real (t + s)
        ∣> k∉Realₜ₊ₛ                  ∶ ⊥
        
      
      --------------------------------------------------------------------------
      -- Compute the minimum cut edge (iₘᵢₙ , kₘᵢₙ) of F
      
      open FixedSubtree 𝓟𝓢𝓒 X j t F-nonfull (j , j∈F) F-fixed

      kₘᵢₙ∈Fixedₜ : kₘᵢₙ ∈ᵤ Fixed t
      kₘᵢₙ∈Fixedₜ = F-fixed kₘᵢₙ∈F

      --------------------------------------------------------------------------
      -- Some notation for comparing edges.

      _≤[_]_ : Edge → 𝕋 → Edge → Set _
      (k , l) ≤[ t ] (p , q) = A k l ▷ σ^ t X l j ≤₊ A p q ▷ σ^ t X q j
      
      _<[_]_ : Edge → 𝕋 → Edge → Set _
      (k , l) <[ t ] (p , q) = A k l ▷ σ^ t X l j <₊ A p q ▷ σ^ t X q j

      _<[_]?_ : ∀ e t f → Dec (e <[ t ] f)
      (k , l) <[ t ]? (p , q) = A k l ▷ σ^ t X l j <₊? A p q ▷ σ^ t X q j

      

      --------------------------------------------------------------------------
      -- The length of the route used by node i at time t + s
      
      lengthₙ : 𝕋 → Edge → ℕ
      lengthₙ s (i , k) = size (σ^ (t + s) X k j)

      lengthₙ-extension : ∀ i {s k l e p ∼₁ ∼₂} →
                          path (σ^ (suc t + s) X k j) ≡ valid (e ∷ p ∣ ∼₁ ∣ ∼₂) →
                          path (σ^ (t + s) X l j) ≈ₚ valid p →
                          lengthₙ (suc s) (i , k) ≡ suc (lengthₙ s (k , l))
      lengthₙ-extension i {s} {k} {l} {e} {p} p[σᵗ⁺¹⁺ˢ]≡kl∷p p[σᵗ⁺ˢXₗⱼ]≈p = begin
        lengthₙ (suc s) (i , k)                ≡⟨⟩
        length (path (σ^ (t + suc s) X k j))   ≡⟨ cong (λ v → length (path (σ^ v X k j))) (+-suc t s) ⟩
        length (path (σ^ (suc t + s) X k j))   ≡⟨ cong length p[σᵗ⁺¹⁺ˢ]≡kl∷p ⟩
        suc (length (valid p))                 ≡⟨ sym (cong suc (length-cong p[σᵗ⁺ˢXₗⱼ]≈p)) ⟩
        suc (length (path (σ^ (t + s) X l j))) ≡⟨⟩
        suc (lengthₙ s (k , l))                ∎
        where open ≡-Reasoning


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
            A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + suc s) X kₘᵢₙ j ≈⟨ ▷-cong _ (Fixed-eq t kₘᵢₙ (suc s) s kₘᵢₙ∈Fixedₜ) ⟩≤
            A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + s)     X kₘᵢₙ j ∎
            where open SPOR ≤₊-poset

      --------------------------------------------------------------------------
      -- A proof that any "real" route ending in a node outside of the fixed
      -- subtree, is not dangerous

      private
        lemma : ∀ {i k l s} → σ^ (t + s) X k j ≈ A k l ▷ σ^ (t + s) X l j →
                eₘᵢₙ ≤[ t + s ] (k , l) → eₘᵢₙ ≤[ t + s ] (i , k)
        lemma {i} {k} {l} {s} eq leq = begin
          A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + s) X kₘᵢₙ j         ≤⟨ leq ⟩
          A k    l    ▷ σ^ (t + s) X l j           ≤⟨ ⊕-absorbs-▷ (A i k) _ ⟩
          A i    k    ▷ (A k l ▷ σ^ (t + s) X l j) ≈⟨ ▷-cong (A i k) (≈-sym eq) ⟩
          A i    k    ▷ σ^ (t + s) X k j           ∎
          where open POR ≤₊-poset
      
      ∈Real-invalid : ∀ s {i k} → k ∈ᵤ Real (t + s) → k ∉ F →
                      path (σ^ (t + s) X k j) ≈ₚ invalid →
                      eₘᵢₙ ≤[ t + s ] (i , k)
      ∈Real-invalid s {i} {k} k∈Rₛ₊ₜ k∉F p[σᵗ⁺ˢXₖⱼ]≈∅ = begin
        A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + s) X kₘᵢₙ j ≤⟨ ⊕-identityˡ _ ⟩
        0#                               ≈⟨ ≈-sym (▷-zero (A i k)) ⟩
        A i    k    ▷ 0#                 ≈⟨ ▷-cong (A i k) (≈-sym (path[r]≈∅⇒r≈0 p[σᵗ⁺ˢXₖⱼ]≈∅)) ⟩
        A i    k    ▷ σ^ (t + s) X k j   ∎
        where open POR ≤₊-poset

      ∈Real-trivial : ∀ s {i k} → k ∈ᵤ Real (t + s) → k ∉ F →
                      path (σ^ (t + s) X k j) ≈ₚ valid [] →
                      eₘᵢₙ ≤[ t + s ] (i , k)
      ∈Real-trivial s {i} {k} k∈Rₛ₊ₜ k∉F p[σᵗ⁺ˢXₖⱼ]≈[]
        with p[σXᵢⱼ]≈[]⇒i≡j (σ^ (t-1 + s) X) k j p[σᵗ⁺ˢXₖⱼ]≈[]
      ... | refl = contradiction j∈F k∉F

      ∈Real : ∀ s i {k} → k ∈ᵤ Real (t + s) → k ∉ F →
                        ∀ {p} → path (σ^ (t + s) X k j) ≈ₚ p →
                        eₘᵢₙ ≤[ t + s ] (i , k)
      ∈Real s i {_} k∈Rₛ₊ₜ k∉F {invalid}  p[σᵗ⁺ˢXₖⱼ]≈∅  = ∈Real-invalid s k∈Rₛ₊ₜ k∉F p[σᵗ⁺ˢXₖⱼ]≈∅
      ∈Real s i {_} k∈Rₛ₊ₜ k∉F {valid []} p[σᵗ⁺ˢXₖⱼ]≈[] = ∈Real-trivial s k∈Rₛ₊ₜ k∉F p[σᵗ⁺ˢXₖⱼ]≈[]
      ∈Real s i {k} k∈Rₛ₊ₜ k∉F {valid ((_ , l) ∷ p ∣ _ ∣ _)} p[σᵗ⁺ˢXₖⱼ]≈kl∷p
        with Real-path {t-1 + s} k∈Rₛ₊ₜ p[σᵗ⁺ˢXₖⱼ]≈kl∷p
      ... | valid ([ _ , l∈Rₛ₊ₜ ]∷ _)
        with Real-alignment (t-1 + s) k∈Rₛ₊ₜ p[σᵗ⁺ˢXₖⱼ]≈kl∷p
      ...   | refl , σᵗ⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢXₗⱼ , p[σᵗ⁺ˢXₗⱼ]≈p with l ∈? F
      ...     | yes l∈F = lemma σᵗ⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢXₗⱼ (eₘᵢₙ-isMinₜ₊ₛ (k∉F , l∈F) s)
      ...     | no  l∉F = lemma σᵗ⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢXₗⱼ (∈Real s k l∈Rₛ₊ₜ l∉F p[σᵗ⁺ˢXₗⱼ]≈p)


      private
        lemma₂ : ∀ {s i k l} → k ∉ F →
                 σ^ (suc t + s) X k j ≈ A k l ▷ (σ^ (t + s) X l j) →
                 eₘᵢₙ ≤[ t + s ] (k , l) →
                 eₘᵢₙ ≤[ t + suc s ] (i , k)
        lemma₂ {s} {i} {k} {l} k∉F σ¹⁺ᵗ⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ eₘᵢₙ≤kl = (begin
          A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + suc s) X kₘᵢₙ j ≈⟨ ▷-cong (A iₘᵢₙ kₘᵢₙ)
                                                   (Fixed-eq t kₘᵢₙ (suc s) s kₘᵢₙ∈Fixedₜ) ⟩
          A iₘᵢₙ kₘᵢₙ ▷ σ^ (t +     s) X kₘᵢₙ j ≤⟨ eₘᵢₙ≤kl ⟩
          A k l ▷ σ^ (t + s) X l j             ≤⟨ ⊕-absorbs-▷ (A i k) (A k l ▷ σ^ (t + s) X l j) ⟩
          A i k ▷ (A k l ▷ σ^ (t + s) X l j)   ≈⟨ ▷-cong (A i k) (≈-sym σ¹⁺ᵗ⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ) ⟩
          A i    k   ▷ σ^ (suc t + s) X k   j  ≈⟨ ≈-reflexive (cong (λ v → A i k ▷ σ^ v X k j)
                                                              (sym (+-suc t s))) ⟩
          A i    k   ▷ σ^ (t + suc s) X k   j  ∎)
          where open POR ≤₊-poset

      Dangerous-predNotReal : ∀ {i k l s} → k ∉ F →
                              σ^ (suc t + s) X k j ≈ A k l ▷ (σ^ (t + s) X l j) →
                              (i , k) ∈ᵤ Dangerous (suc s) → l ∉ᵤ Real (t + s)
      Dangerous-predNotReal {i} {k} {l} {s} k∉F σ¹⁺ᵗ⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ ik∈D₁₊ₛ l∈Rₜ₊ₛ
        with l ∈? F | Dangerous-retraction σ¹⁺ᵗ⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ ik∈D₁₊ₛ
      ... | no  l∉F | l∈Dₛ = <₊⇒≱₊ ik∈D₁₊ₛ (lemma₂ k∉F σ¹⁺ᵗ⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ (∈Real s k l∈Rₜ₊ₛ l∉F ≈ₚ-refl ))
      ... | yes l∈F | l∈Dₛ = <₊⇒≱₊ ik∈D₁₊ₛ (lemma₂ k∉F σ¹⁺ᵗ⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ (eₘᵢₙ-isMinₜ₊ₛ (k∉F , l∈F) s))


      module _ where
      
      -- DangerousJunk nodes are those who are both dangerous and aren't
      -- real, and therefore don't respect the minimal spanning tree
      -- constraints

          DangerousJunk : 𝕋 → Edge → Set ℓ
          DangerousJunk s (i , k) = k ∉ᵤ Real (t + s) × (i , k) ∈ᵤ Dangerous s

          DangerousJunk? : ∀ s → Decidable (DangerousJunk s)
          DangerousJunk? s (i , k) = (∁? (Real? (t + s)) k) ×-dec (Dangerous? s (i , k))

          
          DangerousJunk-extension : ∀ {s i k} → (i , k) ∈ᵤ DangerousJunk (suc s) →
                                    ∃ λ l → (k , l) ∈ᵤ DangerousJunk s
                                            × lengthₙ (suc s) (i , k) ≡ suc (lengthₙ s (k , l))
          DangerousJunk-extension {s} {i} {k} (k∉R₁₊ₛ , k∈D₁₊ₛ)
            with path (σ^ (suc t + s) X k j) | inspect path (σ^ (suc t + s) X k j)
          ... | invalid               | [ p[σᵗ⁺¹⁺ˢ]≡∅ ] = contradiction (Real-cong (Allₑ-resp-≈ₚ invalid (≈ₚ-sym (≈ₚ-reflexive p[σᵗ⁺¹⁺ˢ]≡∅))) (sym (+-suc t s))) k∉R₁₊ₛ
          ... | valid []              | [ p[σᵗ⁺¹⁺ˢ]≡[] ] = contradiction (Real-cong (Allₑ-resp-≈ₚ (valid []) (≈ₚ-sym (≈ₚ-reflexive p[σᵗ⁺¹⁺ˢ]≡[]))) (sym (+-suc t s))) k∉R₁₊ₛ
          ... | valid ((_ , l) ∷ p ∣ _ ∣ _) | [ p[σᵗ⁺¹⁺ˢ]≡kl∷p ]
            with p[σXᵢⱼ]⇒σXᵢⱼ≈AᵢₖXₖⱼ (σ^ (t + s) X) k j (≈ₚ-reflexive p[σᵗ⁺¹⁺ˢ]≡kl∷p)
          ... | (_ , σ¹⁺ᵗ⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢ , p[σᵗ⁺ˢXₗⱼ]≈p) =
            l , (
            Dangerous-predNotReal (¬Real⇒∉F k∉R₁₊ₛ) σ¹⁺ᵗ⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢ k∈D₁₊ₛ ,
            Dangerous-retraction σ¹⁺ᵗ⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢ k∈D₁₊ₛ) ,
            lengthₙ-extension i p[σᵗ⁺¹⁺ˢ]≡kl∷p p[σᵗ⁺ˢXₗⱼ]≈p
            

      
      allJunk : 𝕋 → List Edge
      allJunk s = filter (DangerousJunk? s) (allFinPairs n)

      allJunk-junk : ∀ s → All (DangerousJunk s) (allJunk s)
      allJunk-junk s = filter⁺₁ (DangerousJunk? s) (allFinPairs n)
      
      allJunk-complete : ∀ {s i} → i ∈ᵤ DangerousJunk s → i ∈ₘ allJunk s
      allJunk-complete i∈Jₛ = ∈-filter⁺ (DangerousJunk? _) i∈Jₛ (∈-allFinPairs⁺ _ _)
      
      allJunk-extension : ∀ {t e₁} → e₁ ∈ᵤ DangerousJunk (suc t) →
                          Any (λ e₂ → lengthₙ t e₂ < lengthₙ (suc t) e₁) (allJunk t)
      allJunk-extension k∈J₁₊ₜ with DangerousJunk-extension k∈J₁₊ₜ
      ... | (l , l∈Jₜ , |k|≡1+|l|) =
        lose (allJunk-complete l∈Jₜ) (≤-reflexive (sym |k|≡1+|l|))



      smallestJunk : ∀ t → ∃ (DangerousJunk t) → Edge
      smallestJunk t (e , _) = argmin (lengthₙ t) e (allJunk t)

      smallestJunk-incr : ∀ t ∃t ∃t+1 →
                          lengthₙ t       (smallestJunk t ∃t) <
                          lengthₙ (suc t) (smallestJunk (suc t) ∃t+1)
      smallestJunk-incr t (e₁ , k∈Jₜ) (e₂ , l∈J₁₊ₜ) =
        argmin[xs]<argmin[ys] e₁ (allJunk t)
          (inj₂ (allJunk-extension l∈J₁₊ₜ))
          (All.map (inj₂ ∘ allJunk-extension) (allJunk-junk (suc t)))
