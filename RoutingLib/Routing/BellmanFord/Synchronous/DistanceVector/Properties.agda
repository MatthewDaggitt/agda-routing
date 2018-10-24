open import Algebra using (Semilattice)
open import Algebra.Structures using (IsSemilattice)
import Algebra.FunctionProperties as FunctionProperties
open import Algebra.FunctionProperties.Consequences using (sel⇒idem)
open import Data.Nat using (suc; zero; _+_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Subset using (⊤; _∈_)
open import Data.Fin.Dec using (_∈?_)
open import Data.List using (tabulate)
open import Data.List.Relation.Pointwise using (tabulate⁺)
open import Data.List.Membership.Setoid.Properties
  using (foldr-selective; ∈-tabulate⁻; ∈-tabulate⁺)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃; ∃₂; _,_; _×_; proj₁; proj₂)
open import Function using (_∘_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)
import Relation.Binary.EqReasoning as EqReasoning

open import RoutingLib.Data.List.Properties using (foldr≤ₗe; foldr≤ᵣxs)
open import RoutingLib.Data.Matrix using (SquareMatrix)
open import RoutingLib.Data.List.Relation.Pointwise
  using (foldr⁺)
import RoutingLib.Relation.Binary.Reasoning.PartialOrder as POR

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.RoutingAlgebra
open import RoutingLib.Routing.Model using (AdjacencyMatrix)
import RoutingLib.Routing.Algebra.RoutingAlgebra.Properties as RoutingAlgebraProperties

import RoutingLib.Routing.BellmanFord.Synchronous as BellmanFord

module RoutingLib.Routing.BellmanFord.Synchronous.DistanceVector.Properties
  {a b ℓ n} (algebra : RawRoutingAlgebra a b ℓ)
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (A : AdjacencyMatrix algebra n)
  where

open RawRoutingAlgebra algebra
open IsRoutingAlgebra isRoutingAlgebra
open RoutingAlgebraProperties isRoutingAlgebra

open BellmanFord algebra A
open FunctionProperties _≈_
-- open import Relation.Binary.EqReasoning S

------------------------------------------------------------------------------
-- Identity matrix

Iᵢᵢ-zeᵣ-⊕ : ∀ i → RightZero (I i i) _⊕_
Iᵢᵢ-zeᵣ-⊕ i x rewrite Iᵢᵢ≡0# i = ⊕-zeroʳ x

------------------------------------------------------------------------------
-- Synchronous properties

-- σ either extends the route by going through some k or it chooses a
-- trivial route from the identity matrix
σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ : ∀ X i j → (∃ λ k → σ X i j ≈ A i k ▷ X k j) ⊎ (σ X i j ≈ I i j)
σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ X i j with foldr-selective S ⊕-sel (I i j) _
... | inj₁ σXᵢⱼ≈Iᵢⱼ  = inj₂ σXᵢⱼ≈Iᵢⱼ
... | inj₂ σXᵢⱼ∈extₖ = inj₁ (∈-tabulate⁻ S σXᵢⱼ∈extₖ)

-- Under the following assumptions about ⊕, A▷ₘ always chooses the "best"
-- option with respect to ⊕
σXᵢⱼ≤Aᵢₖ▷Xₖⱼ : ∀ X i j k → σ X i j ≤₊ A i k ▷ X k j
σXᵢⱼ≤Aᵢₖ▷Xₖⱼ X i j k = foldr≤ᵣxs ⊕-semilattice (I i j) (∈-tabulate⁺ S k)

-- After an iteration, the diagonal of the RMatrix is always the identity
σXᵢᵢ≈Iᵢᵢ : ∀ X i → σ X i i ≈ I i i
σXᵢᵢ≈Iᵢᵢ X i with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ X i i
... | inj₂ σXᵢᵢ≈Iᵢᵢ           = σXᵢᵢ≈Iᵢᵢ
... | inj₁ (k , σXᵢᵢ≈AᵢₖXₖⱼ) = begin
  σ X i i         ≈⟨ ≈-sym (foldr≤ₗe ⊕-semilattice (I i i) (tabulate (λ k → A i k ▷ X k i))) ⟩
  σ X i i ⊕ I i i ≈⟨ Iᵢᵢ-zeᵣ-⊕ i (σ X i i) ⟩
  I i i           ∎
  where open EqReasoning S

-- After an iteration, the diagonals of any two RMatrices are equal
σXᵢᵢ≈σYᵢᵢ : ∀ X Y {i j} → i ≡ j → σ X i j ≈ σ Y i j
σXᵢᵢ≈σYᵢᵢ X Y {i} refl = ≈-trans (σXᵢᵢ≈Iᵢᵢ X i) (≈-sym (σXᵢᵢ≈Iᵢᵢ Y i))

-- After an iteration, if one entry is less than the other than it cannot be the identity matrix
σXᵢⱼ<σYᵢⱼ⇒σXᵢⱼ≉Iᵢⱼ : ∀ X Y {i j} → σ X i j <₊ σ Y i j → σ X i j ≉ I i j
σXᵢⱼ<σYᵢⱼ⇒σXᵢⱼ≉Iᵢⱼ X Y {i} {j} σXᵢⱼ<σYᵢⱼ@(σXᵢⱼ≤σYᵢⱼ , σXᵢⱼ≉σYᵢⱼ) with i ≟𝔽 j
... | yes i≡j = contradiction (σXᵢᵢ≈σYᵢᵢ X Y i≡j) σXᵢⱼ≉σYᵢⱼ
... | no  i≢j = <₊⇒≉ (begin
  σ X i j <⟨ σXᵢⱼ<σYᵢⱼ ⟩
  σ Y i j ≤⟨ ⊕-identityˡ (σ Y i j) ⟩
  ∞       ≡⟨ sym (Iᵢⱼ≡∞ (i≢j ∘ sym)) ⟩
  I i j   ∎)
  where open POR ≤₊-poset
