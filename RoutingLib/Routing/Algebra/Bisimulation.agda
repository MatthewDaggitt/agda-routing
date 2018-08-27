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

open import RoutingLib.Asynchronous
import RoutingLib.Asynchronous.Properties as Async
open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.Algebra.WellFormed as WellFormed
import RoutingLib.Routing.BellmanFord as BellmanFord

open RawRoutingAlgebra hiding (_≟_)

module RoutingLib.Routing.Algebra.Bisimulation
  {a₁ b₁ ℓ₁ a₂ b₂ ℓ₂}
  (𝓐 : RawRoutingAlgebra a₁ b₁ ℓ₁)
  (𝓑 : RawRoutingAlgebra a₂ b₂ ℓ₂)
  where

  open RawRoutingAlgebra 𝓐 using () renaming (_≈_ to _≈ᵃ_; _⊕_ to _⊕ᵃ_; _▷_ to _▷ᵃ_; 0# to 0#ᵃ; ∞ to ∞ᵃ)
  open RawRoutingAlgebra 𝓑 using () renaming (_≈_ to _≈ᵇ_; _⊕_ to _⊕ᵇ_; _▷_ to _▷ᵇ_; 0# to 0#ᵇ; ∞ to ∞ᵇ)
  open WellFormed 𝓐
  
  record Bisimilar₁ : Set (lsuc (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂ ⊔ ℓ₁ ⊔ ℓ₂))where
    
    field
      to   : Route 𝓐 → Route 𝓑
      from : Route 𝓑 → Route 𝓐

      toₛ  : ∀ {n} {i j : Fin n} → Step 𝓐 i j → Step 𝓑 i j
      
      to-0#     : to 0#ᵃ ≈ᵇ 0#ᵇ
      to-∞      : to ∞ᵃ  ≈ᵇ ∞ᵇ
      to-cong   : ∀ {x y} → x ≈ᵃ y → to x ≈ᵇ to y
      to-⊕      : ∀ {x y} → WellFormed x → WellFormed y → to x ⊕ᵇ to y ≈ᵇ to (x ⊕ᵃ y)
      to-▷      : ∀ {n} {i j : Fin n} (f : Step 𝓐 i j) x → to (f  ▷ᵃ x) ≈ᵇ toₛ f ▷ᵇ to x
      to-from   : ∀ x → to (from x) ≈ᵇ x

      ⊕-pres-WF : ∀ {x y} → WellFormed x → WellFormed y → WellFormed (x ⊕ᵃ y)



  module _ {n}
    (𝓐↭𝓑 : Bisimilar₁) 
    (Aᵃ : AdjacencyMatrix 𝓐 n)
    (Aᵇ : AdjacencyMatrix 𝓑 n)
    where

    open Bisimilar₁ 𝓐↭𝓑
    open BellmanFord 𝓐 Aᵃ using () renaming (σ to σᵃ; σ∥ to σ∥ᵃ; I to Iᵃ)
    open BellmanFord 𝓑 Aᵇ using () renaming (σ to σᵇ; σ∥ to σ∥ᵇ; I to Iᵇ; σ-cong to σᵇ-cong)
    
    toIᵃ≈Iᵇ : ∀ i j → to (Iᵃ i j) ≈ᵇ Iᵇ i j
    toIᵃ≈Iᵇ i j with j ≟ i
    ... | yes _ = to-0#
    ... | no  _ = to-∞
    
    Iᵢⱼ-wf : ∀ i j → WellFormed (Iᵃ i j)
    Iᵢⱼ-wf i j with j ≟ i
    ... | yes _ = trivial
    ... | no  _ = invalid

    module _ (Aᵃ≡Aᵇ : (∀ i j → toₛ (Aᵃ i j) ≡ Aᵇ i j)) where
    
      to-σ : ∀ {i} X j → to (σᵃ X i j) ≈ᵇ σᵇ (λ k l → to (X k l)) i j
      to-σ {i} X j = begin
          to (σᵃ X i j)
        ≡⟨⟩
          to (foldr _⊕ᵃ_ (Iᵃ i j) (tabulate (λ k → Aᵃ i k ▷ᵃ X k j)))
        ≈⟨ ≈-sym 𝓑 (foldr-map-commute-gen (S 𝓑) {f = to} (⊕-cong 𝓑) ⊕-pres-WF to-⊕ (Iᵢⱼ-wf i j) (tabulate⁺ λ k → extend (Aᵃ i k) (X k j))) ⟩
          foldr _⊕ᵇ_ (to (Iᵃ i j)) (map to (tabulate λ k → Aᵃ i k ▷ᵃ X k j))
        ≈⟨ foldr⁺ (S 𝓑) (⊕-cong 𝓑) (toIᵃ≈Iᵇ i j) (map-tabulate (S 𝓑) to (λ k → Aᵃ i k ▷ᵃ X k j)) ⟩
          foldr _⊕ᵇ_ (Iᵇ i j) (tabulate (λ k → to (Aᵃ i k ▷ᵃ X k j)))
        ≈⟨ foldr⁺ (S 𝓑) (⊕-cong 𝓑) (≈-refl 𝓑) (ListEq.tabulate⁺ (λ k → to-▷ (Aᵃ i k) (X k j)) ) ⟩
          foldr _⊕ᵇ_ (Iᵇ i j) (tabulate (λ k → toₛ (Aᵃ i k) ▷ᵇ to (X k j)))
        ≡⟨ cong (foldr _⊕ᵇ_ (Iᵇ i j)) (tabulate-cong λ k → cong (_▷ᵇ _) (Aᵃ≡Aᵇ i k) ) ⟩
          foldr _⊕ᵇ_ (Iᵇ i j) (tabulate (λ k → Aᵇ i k ▷ᵇ to (X k j)))
        ≡⟨⟩
          σᵇ (λ k l → to (X k l)) i j
        ∎
        where open EqReasoning (S 𝓑)

      σ∥↭ : Bisimilar σ∥ᵃ σ∥ᵇ
      σ∥↭ = record
        { toᵢ       = to ∘_
        ; fromᵢ     = from ∘_
        ; F-cong    = σᵇ-cong

        ; toᵢ-cong  = to-cong ∘_
        ; toᵢ-F     = to-σ
        ; toᵢ-fromᵢ = to-from ∘_
        }

      bisimulation : IsAsynchronouslySafe σ∥ᵃ → IsAsynchronouslySafe σ∥ᵇ
      bisimulation = Async.bisimulation σ∥↭
