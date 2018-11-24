open import Data.Fin using (Fin; _≟_)
open import Data.List using (foldr; tabulate; map)
open import Data.List.Properties using (tabulate-cong)
open import Data.List.All.Properties using (tabulate⁺)
import Data.List.Relation.Equality.Setoid as ListEq
open import Function using (_∘_)
open import Function.Bijection using (Bijection)
open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Relation.Binary using (REL)
open import Relation.Nullary using (yes; no)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; cong)

open import RoutingLib.Data.Matrix using (SquareMatrix)
open import RoutingLib.Data.List.Properties using (foldr-map-commute-gen)
open import RoutingLib.Data.List.Relation.Equality.Setoid using (foldr⁺; map-tabulate)

open import RoutingLib.Iteration.Asynchronous.Dynamic as Async using (Convergent)
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Theorems as Async

open import RoutingLib.Routing using (Network)
open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.Algebra.Comparable as Comparable
import RoutingLib.Routing.VectorBased.Asynchronous as BellmanFord

open RawRoutingAlgebra hiding (_≟_)

module RoutingLib.Routing.Algebra.Bisimulation {a₁ b₁ ℓ₁ a₂ b₂ ℓ₂} where

  record Bisimilar 
    (A : RawRoutingAlgebra a₁ b₁ ℓ₁)
    (B : RawRoutingAlgebra a₂ b₂ ℓ₂)
    : Set (lsuc (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂ ⊔ ℓ₁ ⊔ ℓ₂))where

    open RawRoutingAlgebra A using () renaming (_≈_ to _≈ᵃ_; _⊕_ to _⊕ᵃ_; _▷_ to _▷ᵃ_; 0# to 0#ᵃ; ∞ to ∞ᵃ)
    open RawRoutingAlgebra B using () renaming (_≈_ to _≈ᵇ_; _⊕_ to _⊕ᵇ_; _▷_ to _▷ᵇ_; 0# to 0#ᵇ; ∞ to ∞ᵇ)
    open Comparable A
  
    field
      to        : Route A → Route B
      from      : Route B → Route A

      toₛ       : ∀ {n} {i j : Fin n} → Step A i j → Step B i j
      
      to-0#     : to 0#ᵃ ≈ᵇ 0#ᵇ
      to-∞      : to ∞ᵃ  ≈ᵇ ∞ᵇ
      to-cong   : ∀ {x y} → x ≈ᵃ y → to x ≈ᵇ to y
      to-⊕      : ∀ {x y} → Comparable x y → to x ⊕ᵇ to y ≈ᵇ to (x ⊕ᵃ y)
      to-▷      : ∀ {n} {i j : Fin n} (f : Step A i j) x → to (f  ▷ᵃ x) ≈ᵇ toₛ f ▷ᵇ to x
      to-from   : ∀ x → to (from x) ≈ᵇ x

      -- ⊕-pres-WF : ∀ {x y} → Comparable x y → WellFormed (x ⊕ᵃ y)



  module _ {n}
    {A : RawRoutingAlgebra a₁ b₁ ℓ₁}
    {B : RawRoutingAlgebra a₂ b₂ ℓ₂}
    (A∼B : Bisimilar A B) 
    (Nᵃ : Network A n)
    (Nᵇ : Network B n)
    where
    
    open RawRoutingAlgebra A using () renaming (_≈_ to _≈ᵃ_; _⊕_ to _⊕ᵃ_; _▷_ to _▷ᵃ_; 0# to 0#ᵃ; ∞ to ∞ᵃ)
    open RawRoutingAlgebra B using () renaming (_≈_ to _≈ᵇ_; _⊕_ to _⊕ᵇ_; _▷_ to _▷ᵇ_; 0# to 0#ᵇ; ∞ to ∞ᵇ)
    open Bisimilar A∼B
    open BellmanFord A Nᵃ using () renaming (F′ to Fᵃ; F∥ to F∥ᵃ; I to Iᵃ; Aₜ to Aᵃ)
    open BellmanFord B Nᵇ using () renaming (F′ to Fᵇ; F∥ to F∥ᵇ; I to Iᵇ; Aₜ to Aᵇ; F-cong to Fᵇ-cong)
    
    toIᵃ≈Iᵇ : ∀ i j → to (Iᵃ i j) ≈ᵇ Iᵇ i j
    toIᵃ≈Iᵇ i j with j ≟ i
    ... | yes _ = to-0#
    ... | no  _ = to-∞
    {-
    Iᵢⱼ-wf : ∀ i j → WellFormed (Iᵃ i j)
    Iᵢⱼ-wf i j with j ≟ i
    ... | yes _ = trivial
    ... | no  _ = invalid
    -}
    
    module _ {e p} (Aᵃ≡Aᵇ : (∀ i j → toₛ (Aᵃ e p i j) ≡ Aᵇ e p i j)) where
    
      to-F : ∀ {i} X j → to (Fᵃ e p X i j) ≈ᵇ Fᵇ e p (λ k l → to (X k l)) i j
      to-F {i} X j = begin
          to (Fᵃ e p X i j)
        ≡⟨⟩
          to (foldr _⊕ᵃ_ (Iᵃ i j) (tabulate (λ k → Aᵃ e p i k ▷ᵃ X k j)))
        ≈⟨ ≈-sym B ? ⟩ --(foldr-map-commute-gen (S B) {f = to} (⊕-cong B) ⊕-pres-WF to-⊕ (Iᵢⱼ-wf i j) (tabulate⁺ λ k → extend (Aᵃ i k) (X k j))) ⟩
          foldr _⊕ᵇ_ (to (Iᵃ i j)) (map to (tabulate λ k → Aᵃ e p i k ▷ᵃ X k j))
        ≈⟨ foldr⁺ (S B) (⊕-cong B) (toIᵃ≈Iᵇ i j) (map-tabulate (S B) to (λ k → Aᵃ e p i k ▷ᵃ X k j)) ⟩
          foldr _⊕ᵇ_ (Iᵇ i j) (tabulate (λ k → to (Aᵃ e p i k ▷ᵃ X k j)))
        ≈⟨ foldr⁺ (S B) (⊕-cong B) (≈-refl B) (ListEq.tabulate⁺ (λ k → to-▷ (Aᵃ e p i k) (X k j)) ) ⟩
          foldr _⊕ᵇ_ (Iᵇ i j) (tabulate (λ k → toₛ (Aᵃ e p i k) ▷ᵇ to (X k j)))
        ≡⟨ cong (foldr _⊕ᵇ_ (Iᵇ i j)) (tabulate-cong {n = n} λ k → cong (_▷ᵇ _) (Aᵃ≡Aᵇ i k) ) ⟩
          foldr _⊕ᵇ_ (Iᵇ i j) (tabulate (λ k → Aᵇ e p i k ▷ᵇ to (X k j)))
        ≡⟨⟩
          Fᵇ e p (λ k l → to (X k l)) i j
        ∎
        where open EqReasoning (S B)

    F∥↭ : Async.Bisimilar F∥ᵃ F∥ᵇ
    F∥↭ = record
      { toᵢ       = to ∘_
      ; fromᵢ     = from ∘_

      ; toᵢ-⊥     = toIᵃ≈Iᵇ _
      ; toᵢ-cong  = to-cong ∘_
      ; toᵢ-F     = to-F {!!}
      ; toᵢ-fromᵢ = to-from ∘_
      }

    bisimulation : Convergent F∥ᵃ → Bisimilar A B → Convergent F∥ᵇ
    bisimulation convergent bisim = Async.bisimilar convergent {!!} --(F∥↭ ? {!!})
