--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module contains some basic properties of F, the synchronous iteration
-- underlying vector based routing, under the assumption that the routing
-- algebra is a distance-vector algebra.
--------------------------------------------------------------------------------

import Data.Fin.Properties as Fin
open import Data.Nat.Base using (NonZero; suc)
open import Data.List using (tabulate)
open import Data.List.Membership.Setoid.Properties
  using (foldr-selective; ∈-tabulate⁻; ∈-tabulate⁺)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃; ∃₂; _,_; _×_; proj₁; proj₂)
open import Function using (_∘_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)

open import RoutingLib.Data.List.Properties using (foldr≤ₗe; foldr≤ᵣxs)

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Basics.Network using (AdjacencyMatrix)

module RoutingLib.Routing.VectorBased.Synchronous.DistanceVector.Properties
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  {n} (A : AdjacencyMatrix algebra n)
  where

open RawRoutingAlgebra algebra
open IsRoutingAlgebra isRoutingAlgebra

open import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra isRoutingAlgebra
open import RoutingLib.Routing.VectorBased.Synchronous algebra A

open import Algebra.Definitions _≈_
open import Relation.Binary.Reasoning.PartialOrder ≤₊-poset

------------------------------------------------------------------------------
-- Properties of I, the identity matrix/initial state

⊕-zeroʳ-Iᵢᵢ : ∀ i → RightZero (I i i) _⊕_
⊕-zeroʳ-Iᵢᵢ i x rewrite Iᵢᵢ≡0# i = ⊕-zeroʳ x

------------------------------------------------------------------------------
-- Properties of F, the iteration

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
... | inj₂ FXᵢᵢ≈Iᵢᵢ          = FXᵢᵢ≈Iᵢᵢ
... | inj₁ (k , FXᵢᵢ≈AᵢₖXₖⱼ) = begin-equality
  F X i i         ≈⟨ foldr≤ₗe ⊕-semilattice (I i i) (tabulate (λ k → A i k ▷ X k i)) ⟩
  F X i i ⊕ I i i ≈⟨ ⊕-zeroʳ-Iᵢᵢ i (F X i i) ⟩
  I i i           ∎

-- After an iteration, the diagonals of any two RMatrices are equal
FXᵢᵢ≈FYᵢᵢ : ∀ X Y {i j} → i ≡ j → F X i j ≈ F Y i j
FXᵢᵢ≈FYᵢᵢ X Y {i} refl = ≈-trans (FXᵢᵢ≈Iᵢᵢ X i) (≈-sym (FXᵢᵢ≈Iᵢᵢ Y i))

-- After an iteration, if one entry is less than the other than it cannot be the identity matrix
FXᵢⱼ<FYᵢⱼ⇒FXᵢⱼ≉Iᵢⱼ : ∀ X Y {i j} → F X i j <₊ F Y i j → F X i j ≉ I i j
FXᵢⱼ<FYᵢⱼ⇒FXᵢⱼ≉Iᵢⱼ X Y {i} {j} FXᵢⱼ<FYᵢⱼ@(FXᵢⱼ≤FYᵢⱼ , FXᵢⱼ≉FYᵢⱼ) with i Fin.≟ j
... | yes i≡j = contradiction (FXᵢᵢ≈FYᵢᵢ X Y i≡j) FXᵢⱼ≉FYᵢⱼ
... | no  i≢j = <₊⇒≉ (begin-strict
  F X i j <⟨ FXᵢⱼ<FYᵢⱼ ⟩
  F Y i j ≤⟨ ≤₊-maximum (F Y i j) ⟩
  ∞#      ≡⟨ sym (Iᵢⱼ≡∞ (i≢j ∘ sym)) ⟩
  I i j   ∎)

-- After a non-zero number of iterations, the diagonal is always the trivial route
σᵗXᵢᵢ≈0# : ∀ t .{{_ : NonZero t}} X i → σ t X i i ≈ 0#
σᵗXᵢᵢ≈0# (suc t) X i = ≈-trans (FXᵢᵢ≈Iᵢᵢ (σ t X) i) (≈-reflexive (Iᵢᵢ≡0# i))
