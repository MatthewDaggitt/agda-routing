import Algebra.FunctionProperties as FunctionProperties
open import Data.Nat using (suc; zero; _+_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Subset using (⊤; _∈_)
open import Data.Fin.Dec using (_∈?_)
open import Data.List using (tabulate)
open import Data.List.Relation.Pointwise using (tabulate⁺)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃; ∃₂; _,_; _×_; proj₁; proj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)
open import Algebra.FunctionProperties.Consequences using (sel⇒idem)

open import RoutingLib.Algebra using (Semilattice)
open import RoutingLib.Algebra.Structures using (IsSemilattice)
open import RoutingLib.Routing.Definitions
open import RoutingLib.Data.List.Properties using (foldr≤ₗe; foldr≤ᵣxs)
open import RoutingLib.Data.List.Membership.Setoid.Properties
  using (foldr-∈; ∈-tabulate⁻; ∈-tabulate⁺)
open import RoutingLib.Data.List.Relation.Pointwise
  using (foldr⁺)

import RoutingLib.Routing.BellmanFord as BellmanFord

module RoutingLib.Routing.BellmanFord.Properties
  {a b ℓ n-1} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  (𝓡𝓟 : RoutingProblem 𝓡𝓐 n-1)
  where

  -----------
  -- Setup --
  -----------

  open RoutingProblem 𝓡𝓟
  open BellmanFord 𝓡𝓟
  open FunctionProperties _≈_
  
  abstract

    ---------------------
    -- Identity matrix --
    ---------------------

    Iᵢⱼ≈0⊎1 : ∀ i j → I i j ≈ 0# ⊎ I i j ≈ 1#
    Iᵢⱼ≈0⊎1 i j with j ≟𝔽 i
    ... | yes _ = inj₂ ≈-refl
    ... | no  _ = inj₁ ≈-refl
    
    Iᵢᵢ≡1# : ∀ i → I i i ≡ 1#
    Iᵢᵢ≡1# i with i ≟𝔽 i
    ... | yes _   = refl
    ... | no  i≢i = contradiction refl i≢i
    
    Iᵢⱼ≡0# : ∀ {i j} → j ≢ i → I i j ≡ 0#
    Iᵢⱼ≡0# {i} {j} i≢j with j ≟𝔽 i
    ... | yes i≡j = contradiction i≡j i≢j
    ... | no  _   = refl

    Iᵢᵢ-idᵣ-⊕ : RightZero 1# _⊕_ → ∀ i → RightZero (I i i) _⊕_
    Iᵢᵢ-idᵣ-⊕ 1#-anᵣ-⊕ i x rewrite Iᵢᵢ≡1# i = 1#-anᵣ-⊕ x

    Iᵢⱼ≡Iₖₗ : ∀ {i j k l} → j ≢ i → l ≢ k → I i j ≡ I k l
    Iᵢⱼ≡Iₖₗ j≢i l≢k = trans (Iᵢⱼ≡0# j≢i) (sym (Iᵢⱼ≡0# l≢k))

    
    ----------------------------
    -- Synchronous properties --
    ----------------------------

    -- σ respects the underlying matrix equality
    σ-cong : ∀ {X Y} → X ≈ₘ Y → σ X ≈ₘ σ Y
    σ-cong X≈Y i j = foldr⁺
      _≈_ ⊕-cong ≈-refl (tabulate⁺ (λ k → ▷-cong (A i k) (X≈Y k j)))
    
    -- σ either extends the route by going through some k or it chooses a
    -- trivial route from the identity matrix
    σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ : Selective _⊕_ → ∀ X i j →
                       (∃ λ k → σ X i j ≈ A i k ▷ X k j) ⊎ (σ X i j ≈ I i j)
    σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ ⊕-sel X i j with foldr-∈ S ⊕-sel (I i j) _
    ... | inj₁ σXᵢⱼ≈Iᵢⱼ  = inj₂ σXᵢⱼ≈Iᵢⱼ
    ... | inj₂ σXᵢⱼ∈extₖ = inj₁ (∈-tabulate⁻ S σXᵢⱼ∈extₖ)

    -- Under the following assumptions about ⊕, A▷ₘ always chooses the "best"
    -- option with respect to ⊕
    σXᵢⱼ≤Aᵢₖ▷Xₖⱼ : IsSemilattice _≈_ _⊕_ →
                   ∀ X i j k → σ X i j ≤₊ A i k ▷ X k j
    σXᵢⱼ≤Aᵢₖ▷Xₖⱼ ⊕-isSemilattice X i j k =
      foldr≤ᵣxs (record {isSemilattice = ⊕-isSemilattice})
        (I i j) (∈-tabulate⁺ S (λ k → A i k ▷ X k j) k)

    -- After an iteration, the diagonal of the RMatrix is always the identity
    σXᵢᵢ≈Iᵢᵢ : Selective _⊕_ → Associative _⊕_ → Commutative _⊕_ →
               RightZero 1# _⊕_ → ∀ X i → σ X i i ≈ I i i
    σXᵢᵢ≈Iᵢᵢ ⊕-sel ⊕-assoc ⊕-comm 1#-anᵣ-⊕ X i with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ ⊕-sel X i i
    ... | inj₂ σXᵢᵢ≈Iᵢᵢ           = σXᵢᵢ≈Iᵢᵢ
    ... | inj₁ (k , σXᵢᵢ≈AᵢₖXₖⱼ) = begin
      σ X i i         ≈⟨ ≈-sym (foldr≤ₗe ⊕-semilattice (I i i) (tabulate (λ k → A i k ▷ X k i))) ⟩
      σ X i i ⊕ I i i ≈⟨ Iᵢᵢ-idᵣ-⊕ 1#-anᵣ-⊕ i (σ X i i) ⟩
      I i i           ∎
      where
      open import Relation.Binary.EqReasoning S
      ⊕-semilattice : Semilattice _ _
      ⊕-semilattice = record
        { isSemilattice = record
          { isBand = record
            { isSemigroup = record
              { isEquivalence = ≈-isEquivalence
              ; assoc         = ⊕-assoc
              ; ∙-cong        = ⊕-cong
              }
            ; idem = sel⇒idem S ⊕-sel
            }
          ; comm = ⊕-comm
          }
        }
      
    -- After an iteration, the diagonals of any two RMatrices are equal
    σXᵢᵢ≈σYᵢᵢ : Selective _⊕_ → Associative _⊕_ →
                Commutative _⊕_ → RightZero 1# _⊕_ →
                ∀ X Y i → σ X i i ≈ σ Y i i
    σXᵢᵢ≈σYᵢᵢ ⊕-sel ⊕-assoc ⊕-comm 1#-anᵣ-⊕ X Y i =
      ≈-trans
        (σXᵢᵢ≈Iᵢᵢ ⊕-sel ⊕-assoc ⊕-comm 1#-anᵣ-⊕ X i)
        (≈-sym (σXᵢᵢ≈Iᵢᵢ ⊕-sel ⊕-assoc ⊕-comm 1#-anᵣ-⊕ Y i))
