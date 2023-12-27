open import Data.Nat using (ℕ; NonZero; zero; suc; z≤n; s≤s; _+_; _<_; _≤_)
open import Data.Nat.Properties using (<⇒≱; +-suc; m≤m+n; <-transˡ; +-comm; module ≤-Reasoning)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (any?)
open import Data.Fin.Subset using (Subset; _∈_; _∉_; _∪_; ⁅_⁆)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Product using (_,_; _×_; ∃; ∃₂)
open import Data.List.Membership.Propositional.Properties using (∈-filter⁺)
open import Function using (_∘_)
open import Relation.Nullary using (Dec; ¬_; yes; no; _×-dec_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary
  using (Empty; Decidable) renaming (_∈_ to _∈ᵤ_; _∉_ to _∉ᵤ_; _⊆_ to _⊆ᵤ_)
open import Relation.Unary.Properties using (∁?; _∩?_)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; [_]; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; cong; subst; refl; sym; trans; inspect; [_]; module ≡-Reasoning)
import Relation.Binary.Reasoning.PartialOrder as POR

open import RoutingLib.Data.Matrix using (SquareMatrix)
open import RoutingLib.Routing.Basics.Path.CertifiedI.AllVertices
open import RoutingLib.Routing.Basics.Path.CertifiedI.Properties
open import RoutingLib.Data.Fin.Subset using (Nonfull)
open import RoutingLib.Data.List using (allFinPairs)
open import RoutingLib.Data.List.Membership.Propositional.Properties using (∈-allFinPairs⁺)
import RoutingLib.Function.Reasoning as FunctionalReasoning
open import RoutingLib.Data.Nat.Properties

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Prelude using (RoutingMatrix; AdjacencyMatrix)
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.Convergence.Prelude as Prelude
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.Convergence.Step1_NodeSets as Step1_NodeSets
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.Convergence.Step2_ConvergedSubtree as Step2_ConvergedSubtree
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.Convergence.Step3_DangerousNodes as Step3_DangerousNodes
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.Convergence.Step4_InductiveStep as Step4_InductiveStep

module RoutingLib.Routing.VectorBased.Synchronous.PathVector.Convergence.Step5_Distributivity
  {a b ℓ n-1} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (isPathAlgebra : IsCertifiedPathAlgebra algebra (suc n-1))
  (A : AdjacencyMatrix algebra (suc n-1))
  (X : RoutingMatrix   algebra (suc n-1))
  (j : Fin (suc n-1))
  (open Prelude isRoutingAlgebra isPathAlgebra A)
  (open Step1_NodeSets isRoutingAlgebra isPathAlgebra A X j)
  (isIncreasing  : IsIncreasing algebra)
  (isDistributive : IsDistributive algebra)
  (t : ℕ)
  (C : Subset n)
  (C-nonFull : Nonfull C)
  (j∈C : j ∈ C)
  (i∈𝓚 : ∀ s i → i ∈ᵤ 𝓚 (t + s))
  (C⊆𝓒ₜ : ∀ {i} → i ∈ C → i ∈ᵤ 𝓒 t)
  (C⊆𝓖ₜ : ∀ {i} → i ∈ C → i ∈ᵤ 𝓖 t)
  where

open import RoutingLib.Routing.Basics.Assignment
open Notation X j
open POR ≤₊-poset

--------------------------------------------------------------------------
-- Compute the minimum cut edge (iₘᵢₙ , kₘᵢₙ) of C

open Step2_ConvergedSubtree isRoutingAlgebra isPathAlgebra A X j t C C-nonFull j∈C
open Step3_DangerousNodes isRoutingAlgebra isPathAlgebra A X j isIncreasing t C C-nonFull j∈C C⊆𝓒ₜ
open Step4_InductiveStep isRoutingAlgebra isPathAlgebra A X j t C C-nonFull j∈C C⊆𝓒ₜ

▷-mono-≤ : ∀ {i j : Fin n} (f : Step i j) {x y} → x ≤₊ y → f ▷ x ≤₊ f ▷ y
▷-mono-≤ = distrib⇒▷-mono-≤ isDistributive

i⇨[p]⇨j∧i∉C⇒eₘᵢₙ≤w[p] : ∀ s p {i} → i ⇨[ p ]⇨ j → i ∉ C → A iₘᵢₙ kₘᵢₙ ▷ σ (t + s) X kₘᵢₙ j ≤₊ weight A p
i⇨[p]⇨j∧i∉C⇒eₘᵢₙ≤w[p] s invalid   invalid       i∉C = ≤₊-maximum (weightₑ (t + s) eₘᵢₙ)
i⇨[p]⇨j∧i∉C⇒eₘᵢₙ≤w[p] s (valid p) (valid i⇨p⇨j) i∉C = rec p i⇨p⇨j i∉C
  where
  rec : ∀ p {i} → i ⇨[ᵛ p ]⇨ j → i ∉ C → weightₑ (t + s) eₘᵢₙ ≤₊ weight A (valid p)
  rec []                    ⇨[]⇨        j∉C = contradiction j∈C j∉C
  rec ((i , k) ∷ p ∣ _ ∣ _) (⇨∷⇨ k⇨p⇨j) i∉C with k ∈? C
  ... | no  k∉C = begin
    weightₑ (t + s) eₘᵢₙ       ≤⟨ rec p k⇨p⇨j k∉C ⟩
    weight A (valid p)         ≤⟨ isIncreasing (A i k) (weight A (valid p)) ⟩
    A i k ▷ weight A (valid p) ∎
  ... | yes k∈C = begin
    weightₑ (t + s) eₘᵢₙ       ≤⟨ c↷C⇒eₘᵢₙ≤e (i∉C , k∈C) s ⟩
    weightₑ (t + s) (i , k)    ≡⟨⟩
    A i k ▷ σ (t + s) X k j    ≤⟨ ▷-mono-≤ (A i k) (C⊆𝓖ₜ k∈C s p k⇨p⇨j) ⟩
    A i k ▷ weight A (valid p) ∎
  
eₘᵢₙ≤ₜ₊ₛe : ∀ s k → eₘᵢₙ ≤[ t + s ] (iₘᵢₙ , k)
eₘᵢₙ≤ₜ₊ₛe s k with k ∈? C
... | yes k∈C = c↷C⇒eₘᵢₙ≤e (iₘᵢₙ∉C , k∈C) s
... | no  k∉C = let (σᵗ⁺ˢXₖⱼᶜ , i⇨[p]⇨j , _) = i∈𝓚 s k in begin
  weightₑ (t + s) eₘᵢₙ       ≤⟨ i⇨[p]⇨j∧i∉C⇒eₘᵢₙ≤w[p] s (path σᵗ⁺ˢXₖⱼ) i⇨[p]⇨j k∉C ⟩
  weight A (path σᵗ⁺ˢXₖⱼ)    ≈⟨ σᵗ⁺ˢXₖⱼᶜ ⟩
  σᵗ⁺ˢXₖⱼ                    ≤⟨ isIncreasing (A iₘᵢₙ k) σᵗ⁺ˢXₖⱼ ⟩
  A iₘᵢₙ k ▷ σᵗ⁺ˢXₖⱼ         ≡⟨⟩
  weightₑ (t + s) (iₘᵢₙ , k) ∎
  where σᵗ⁺ˢXₖⱼ = σ (t + s) X k j

iₘᵢₙ∈𝓖₁₊ₜ : iₘᵢₙ ∈ᵤ 𝓖 (suc t)
iₘᵢₙ∈𝓖₁₊ₜ s p iₘᵢₙ⇨p⇨j = rec p iₘᵢₙ iₘᵢₙ⇨p⇨j iₘᵢₙ∉C
  where
  rec : ∀ p i → i ⇨[ᵛ p ]⇨ j → i ∉ C → σ (suc t + s) X iₘᵢₙ j ≤₊ weight A (valid p)
  rec []                    i ⇨[]⇨        i∉C = contradiction j∈C i∉C
  rec ((i , k) ∷ p ∣ _ ∣ _) i (⇨∷⇨ k⇨p⇨j) i∉C with k ∈? C
  ... | yes k∈C = begin
    σ (suc t + s) X iₘᵢₙ j           ≡⟨ cong (λ v → σ (v + s) X iₘᵢₙ j) (+-comm 1 t) ⟩
    σ (t + 1 + s) X iₘᵢₙ j           ≈⟨ iₘᵢₙ-pred 0 eₘᵢₙ≤ₜ₊ₛe s ⟩
    A iₘᵢₙ kₘᵢₙ ▷ σ (t + s) X kₘᵢₙ j ≤⟨ c↷C⇒eₘᵢₙ≤e (i∉C , k∈C) s ⟩
    A i    k    ▷ σ (t + s) X k    j ≤⟨ ▷-mono-≤ (A i k) (C⊆𝓖ₜ k∈C s p k⇨p⇨j) ⟩
    A i    k    ▷ weight A (valid p) ∎
  ... | no  k∉C = begin
    σ (suc t + s) X iₘᵢₙ j     ≤⟨ rec p k k⇨p⇨j k∉C ⟩
    weight A (valid p)         ≤⟨ isIncreasing (A i k) (weight A (valid p)) ⟩
    A i k ▷ weight A (valid p) ∎

