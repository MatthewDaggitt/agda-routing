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
open import RoutingLib.Routing using (AdjacencyMatrix)
import RoutingLib.Routing.Algebra.RoutingAlgebra.Properties as RoutingAlgebraProperties

import RoutingLib.Routing.VectorBased.Synchronous as VectorBased

module RoutingLib.Routing.VectorBased.Core.Properties
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  {n} (A : AdjacencyMatrix algebra n)
  where

open RawRoutingAlgebra algebra
open IsRoutingAlgebra isRoutingAlgebra
open RoutingAlgebraProperties isRoutingAlgebra

open VectorBased algebra A
open FunctionProperties _≈_

------------------------------------------------------------------------------
-- Identity matrix

Iᵢᵢ-zeᵣ-⊕ : ∀ i → RightZero (I i i) _⊕_
Iᵢᵢ-zeᵣ-⊕ i x rewrite Iᵢᵢ≡0# i = ⊕-zeroʳ x

------------------------------------------------------------------------------
-- Synchronous properties

-- F either extends the route by going through some k or it chooses a
-- trivial route from the identity matrix
FXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ : ∀ X i j → (∃ λ k → F X i j ≈ A i k ▷ X k j) ⊎ (F X i j ≈ I i j)
FXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ X i j with foldr-selective S ⊕-sel (I i j) _
... | inj₁ FXᵢⱼ≈Iᵢⱼ  = inj₂ FXᵢⱼ≈Iᵢⱼ
... | inj₂ FXᵢⱼ∈extₖ = inj₁ (∈-tabulate⁻ S FXᵢⱼ∈extₖ)

-- Under the following assumptions about ⊕, A▷ₘ always chooses the "best"
-- option with respect to ⊕
FXᵢⱼ≤Aᵢₖ▷Xₖⱼ : ∀ X i j k → F X i j ≤₊ A i k ▷ X k j
FXᵢⱼ≤Aᵢₖ▷Xₖⱼ X i j k = foldr≤ᵣxs ⊕-semilattice (I i j) (∈-tabulate⁺ S k)

-- After an iteration, the diagonal of the RMatrix is always the identity
FXᵢᵢ≈Iᵢᵢ : ∀ X i → F X i i ≈ I i i
FXᵢᵢ≈Iᵢᵢ X i with FXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ X i i
... | inj₂ FXᵢᵢ≈Iᵢᵢ           = FXᵢᵢ≈Iᵢᵢ
... | inj₁ (k , FXᵢᵢ≈AᵢₖXₖⱼ) = begin
  F X i i         ≈⟨ ≈-sym (foldr≤ₗe ⊕-semilattice (I i i) (tabulate (λ k → A i k ▷ X k i))) ⟩
  F X i i ⊕ I i i ≈⟨ Iᵢᵢ-zeᵣ-⊕ i (F X i i) ⟩
  I i i           ∎
  where open EqReasoning S

-- After an iteration, the diagonals of any two RMatrices are equal
FXᵢᵢ≈FYᵢᵢ : ∀ X Y {i j} → i ≡ j → F X i j ≈ F Y i j
FXᵢᵢ≈FYᵢᵢ X Y {i} refl = ≈-trans (FXᵢᵢ≈Iᵢᵢ X i) (≈-sym (FXᵢᵢ≈Iᵢᵢ Y i))

-- After an iteration, if one entry is less than the other than it cannot be the identity matrix
FXᵢⱼ<FYᵢⱼ⇒FXᵢⱼ≉Iᵢⱼ : ∀ X Y {i j} → F X i j <₊ F Y i j → F X i j ≉ I i j
FXᵢⱼ<FYᵢⱼ⇒FXᵢⱼ≉Iᵢⱼ X Y {i} {j} FXᵢⱼ<FYᵢⱼ@(FXᵢⱼ≤FYᵢⱼ , FXᵢⱼ≉FYᵢⱼ) with i ≟𝔽 j
... | yes i≡j = contradiction (FXᵢᵢ≈FYᵢᵢ X Y i≡j) FXᵢⱼ≉FYᵢⱼ
... | no  i≢j = <₊⇒≉ (begin
  F X i j <⟨ FXᵢⱼ<FYᵢⱼ ⟩
  F Y i j ≤⟨ ⊕-identityˡ (F Y i j) ⟩
  ∞       ≡⟨ sym (Iᵢⱼ≡∞ (i≢j ∘ sym)) ⟩
  I i j   ∎)
  where open POR ≤₊-poset
