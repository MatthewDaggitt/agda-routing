open import Algebra using (Semilattice)
open import Algebra.Structures using (IsSemilattice)
import Algebra.FunctionProperties as FunctionProperties
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
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)
open import Algebra.FunctionProperties.Consequences using (sel⇒idem)

open import RoutingLib.Data.List.Properties using (foldr≤ₗe; foldr≤ᵣxs)
open import RoutingLib.Data.Matrix using (SquareMatrix)
open import RoutingLib.Data.List.Relation.Pointwise
  using (foldr⁺)

open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra as RoutingAlgebraProperties

import RoutingLib.Routing.BellmanFord as BellmanFord

module RoutingLib.Routing.BellmanFord.Properties
  {a b ℓ n}
  (algebra : RoutingAlgebra a b ℓ)
  (A : SquareMatrix (RoutingAlgebra.Step algebra) n)
  where

-----------
-- Setup --
-----------

open RoutingAlgebra algebra
open RoutingAlgebraProperties algebra

open BellmanFord rawRoutingAlgebra A
open FunctionProperties _≈_
open import Relation.Binary.EqReasoning S

abstract

  ------------------------------------------------------------------------------
  -- Identity matrix

  Iᵢⱼ≈0⊎∞ : ∀ i j → (I i j ≈ 0#) ⊎ (I i j ≈ ∞)
  Iᵢⱼ≈0⊎∞ i j with j ≟𝔽 i
  ... | yes _ = inj₁ ≈-refl
  ... | no  _ = inj₂ ≈-refl

  Iᵢᵢ≡0# : ∀ i → I i i ≡ 0#
  Iᵢᵢ≡0# i with i ≟𝔽 i
  ... | yes _   = refl
  ... | no  i≢i = contradiction refl i≢i

  Iᵢⱼ≡∞ : ∀ {i j} → j ≢ i → I i j ≡ ∞
  Iᵢⱼ≡∞ {i} {j} i≢j with j ≟𝔽 i
  ... | yes i≡j = contradiction i≡j i≢j
  ... | no  _   = refl

  Iᵢᵢ-zeᵣ-⊕ : ∀ i → RightZero (I i i) _⊕_
  Iᵢᵢ-zeᵣ-⊕ i x rewrite Iᵢᵢ≡0# i = ⊕-zeroʳ x

  Iᵢⱼ≡Iₖₗ : ∀ {i j k l} → j ≢ i → l ≢ k → I i j ≡ I k l
  Iᵢⱼ≡Iₖₗ j≢i l≢k = trans (Iᵢⱼ≡∞ j≢i) (sym (Iᵢⱼ≡∞ l≢k))


  ------------------------------------------------------------------------------
  -- Synchronous properties

  -- σ respects the underlying matrix equality
  σ-cong : ∀ {X Y} → X ≈ₘ Y → σ X ≈ₘ σ Y
  σ-cong X≈Y i j = foldr⁺
    _≈_ ⊕-cong ≈-refl (tabulate⁺ (λ k → ▷-cong (A i k) (X≈Y k j)))

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

  -- After an iteration, the diagonals of any two RMatrices are equal
  σXᵢᵢ≈σYᵢᵢ : ∀ X Y i → σ X i i ≈ σ Y i i
  σXᵢᵢ≈σYᵢᵢ X Y i = ≈-trans (σXᵢᵢ≈Iᵢᵢ X i) (≈-sym (σXᵢᵢ≈Iᵢᵢ Y i))
