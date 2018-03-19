open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _∸_; _<_; _≤_)
open import Data.Nat.Properties using (+-identityʳ; +-comm; +-assoc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Subset using (Subset; _∈_; _∉_; _∪_)
open import Data.Fin.Dec using (_∈?_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (_,_; _×_; ∃; ∃₂; proj₁; proj₂)
open import Data.List using (List; filter; allFin)
open import Data.List.All using (All)
open import Data.List.All.Properties using (filter⁺₁)
open import Data.List.Any using (Any)
open import Data.List.Any.Membership.Propositional using (_⊆_)
open import Data.List.Any.Membership.Propositional.Properties using ()
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary
  using (∁; ∁?; Decidable; U) renaming (_∈_ to _∈ᵤ_; _∉_ to _∉ᵤ_; _⊆_ to _⊆ᵤ_)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; subst; refl; sym; trans; inspect; [_])
import Relation.Binary.PartialOrderReasoning as POR
import Relation.Binary.EqReasoning as EqReasoning

open import RoutingLib.Data.SimplePath
  using (SimplePath; []; _∷_∣_∣_; invalid; valid; notThere; notHere; continue)
  renaming (_∈_ to _∈ₚ_)
open import RoutingLib.Data.SimplePath.Relation.Equality
open import RoutingLib.Data.SimplePath.Relation.Subpath
open import RoutingLib.Data.SimplePath.All
open import RoutingLib.Data.SimplePath.Properties
  using (∉-resp-≈ₚ)
open import RoutingLib.Data.Fin.Subset using (size; Nonfull)
open import RoutingLib.Relation.Unary using (_∩?_)

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

      open FixedSubtree 𝓟𝓢𝓒 X j t F-nonfull (j , j∈F) F-fixed

      _<[_]_ : Node → 𝕋 → Node → Set _
      k <[ s ] l = A iₘᵢₙ k ▷ σ^ (t + s) X k j <₊ A iₘᵢₙ l ▷ σ^ (t + s) X l j
      
      DangerousJunk : 𝕋 → Node → Set _
      DangerousJunk s k = k ∉ᵤ Real (t + s) × k <[ s ] kₘᵢₙ

      DangerousJunk? : ∀ s → Decidable (DangerousJunk s)
      DangerousJunk? s = (∁? (Real? (t + s))) ∩?
                         (λ k → A iₘᵢₙ k ▷ σ^ (t + s) X k j <₊? A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + s) X kₘᵢₙ j)

      postulate DangerousJunk-extension : ∀ {s k} → k ∈ᵤ DangerousJunk (suc s) →
                                ∃ λ l → σ^ (suc s) X k j ≈ A k l ▷ σ^ s X l j ×
                                        l ∈ᵤ DangerousJunk s

      {-
      DangerousJunk-extension {s} {k} (k∈Rₜ₊ₛ , k<kₘᵢₙ)
        with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ (σ^ s X) k j
      ... | inj₂ σ¹⁺ˢXₖⱼ≈Iₖⱼ             = {!!} , {!!}
      ... | inj₁ (l , σ¹⁺ˢXₖⱼ≈AₖₗσˢXₗⱼ)  = {!!}
      -}
      
      {-
      ∈Real-invalid : ∀ s i k → k ∈ᵤ Real (t + s) → k ∉ F →
                      path (σ^ (t + s) X k j) ≈ₚ invalid →
                      A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + s) X kₘᵢₙ j ≤₊ A i k ▷ σ^ (t + s) X k j
      ∈Real-invalid s i k k∈Rₛ₊ₜ k∉F p[σᵗ⁺ˢXₖⱼ]≈∅ = begin
        A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + s) X kₘᵢₙ j ≤⟨ ⊕-identityˡ _ ⟩
        0#                                ≈⟨ ≈-sym (▷-zero (A i k)) ⟩
        A i    k    ▷ 0#                  ≈⟨ ▷-cong (A i k) (≈-sym (path[r]≈∅⇒r≈0 p[σᵗ⁺ˢXₖⱼ]≈∅)) ⟩
        A i    k    ▷ σ^ (t + s) X k j    ∎
        where open POR ≤₊-poset

      ∈Real-trivial : ∀ s i k → k ∈ᵤ Real (t + s) → k ∉ F →
                      path (σ^ (t + s) X k j) ≈ₚ valid [] →
                      A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + s) X kₘᵢₙ j ≤₊ A i k ▷ σ^ (t + s) X k j
      ∈Real-trivial s i k k∈Rₛ₊ₜ k∉F p[σᵗ⁺ˢXₖⱼ]≈[]
        with p[σXᵢⱼ]≈[]⇒i≡j (σ^ (t-1 + s) X) k j p[σᵗ⁺ˢXₖⱼ]≈[]
      ... | refl = contradiction j∈F k∉F

      ∈Real : ∀ s i k → k ∈ᵤ Real (t + s) → k ∉ F → ∀ {p} → path (σ^ (t + s) X k j) ≈ₚ p →
              A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + s) X kₘᵢₙ j ≤₊ A i k ▷ σ^ (t + s) X k j
      ∈Real s i k k∈Rₛ₊ₜ k∉F {invalid}  p[σᵗ⁺ˢXₖⱼ]≈∅  = ∈Real-invalid s i k k∈Rₛ₊ₜ k∉F p[σᵗ⁺ˢXₖⱼ]≈∅
      ∈Real s i k k∈Rₛ₊ₜ k∉F {valid []} p[σᵗ⁺ˢXₖⱼ]≈[] = ∈Real-trivial s i k k∈Rₛ₊ₜ k∉F p[σᵗ⁺ˢXₖⱼ]≈[]
      ∈Real s i k k∈Rₛ₊ₜ k∉F {valid ((_ , l) ∷ p ∣ _ ∣ _)} p[σᵗ⁺ˢXₖⱼ]≈kl∷p
        with Real-path {t-1 + s} k∈Rₛ₊ₜ p[σᵗ⁺ˢXₖⱼ]≈kl∷p
      ... | valid ([ _ , l∈Rₛ₊ₜ ]∷ _)
        with Real-alignment (t-1 + s) k∈Rₛ₊ₜ p[σᵗ⁺ˢXₖⱼ]≈kl∷p
      ...   | refl , σᵗ⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢXₗⱼ , p[σᵗ⁺ˢXₗⱼ]≈p with l ∈? F
      ...     | yes l∈F = begin
        A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + s) X kₘᵢₙ j        ≤⟨ eₘᵢₙ-isMinₜ₊ₛ (k∉F , l∈F) s ⟩
        A k    l    ▷ σ^ (t + s) X l j           ≤⟨ ⊕-absorbs-▷ (A i k) _ ⟩
        A i    k    ▷ (A k l ▷ σ^ (t + s) X l j) ≈⟨ ▷-cong (A i k) (≈-sym σᵗ⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢXₗⱼ) ⟩
        A i    k    ▷ σ^ (t + s) X k j           ∎
        where open POR ≤₊-poset
      ... | no  l∉F = begin
        A iₘᵢₙ kₘᵢₙ ▷ σ^ (t + s) X kₘᵢₙ j        ≤⟨ ∈Real s k l l∈Rₛ₊ₜ l∉F p[σᵗ⁺ˢXₗⱼ]≈p ⟩
        A k    l    ▷ σ^ (t + s) X l j           ≤⟨ ⊕-absorbs-▷ (A i k) _ ⟩
        A i    k    ▷ (A k l ▷ σ^ (t + s) X l j) ≈⟨ ▷-cong (A i k) (≈-sym σᵗ⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢXₗⱼ) ⟩
        A i    k    ▷ σ^ (t + s) X k j           ∎
        where open POR ≤₊-poset
      -}

      allJunk : 𝕋 → List Node
      allJunk s = filter (DangerousJunk? s) (allFin n)

      allJunk-junk : ∀ s → All (DangerousJunk s) (allJunk s)
      allJunk-junk s = filter⁺₁ (DangerousJunk? s) (allFin n)

      
      {-
      allJunk-decr : ∀ s → All (λ k → Any (λ l → {!!}) (allJunk s)) (allJunk (suc s))
      allJunk-decr = {!!}

      smallestJunk : 𝕋 → Node
      smallestJunk s = {!argmin ? ? ?!}
      -}
