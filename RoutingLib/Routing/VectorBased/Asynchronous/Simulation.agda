--------------------------------------------------------------------------------
-- Agda routing library
--
-- The proof that if algebra A simulates algebra B then if the vector-based
-- protocol based on A converges then so does the vector-based protocol based
-- on algebra B. This is based on a reduction to the simulation results for
-- general dynamic asynchronous iterations found in `RoutingLib.Iteration`.
--------------------------------------------------------------------------------

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.Simulation

module RoutingLib.Routing.VectorBased.Asynchronous.Simulation
  {a₁ b₁ ℓ₁ a₂ b₂ ℓ₂}
  {A : RawRoutingAlgebra a₁ b₁ ℓ₁}
  {B : RawRoutingAlgebra a₂ b₂ ℓ₂}
  (A⇉B : A Simulates B)
  where

open import Data.Fin using (Fin; _≟_)
open import Data.Fin.Subset using (Subset)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.List using (foldr; tabulate; map)
open import Data.List.Properties using (tabulate-cong)
open import Data.List.All using (All; []; _∷_)
open import Data.List.All.Properties using (tabulate⁺)
open import Data.Nat using (ℕ)
import Data.List.Relation.Equality.Setoid as ListEq
open import Function using (_∘_)
open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Relation.Binary using (REL)
open import Relation.Nullary using (yes; no)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; cong)

open import RoutingLib.Routing using (Network)
open import RoutingLib.Data.Matrix using (SquareMatrix)
open import RoutingLib.Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
import RoutingLib.Data.List.Relation.Unary.AllPairs.Properties as AllPairs
open import RoutingLib.Data.List.Properties using (foldr-map-commute-gen₂)
open import RoutingLib.Data.List.Relation.Binary.Equality.Setoid using (foldr⁺; map-tabulate)

open import RoutingLib.Iteration.Asynchronous.Dynamic as Async using (Epoch; Convergent)
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence as Async

import RoutingLib.Routing.Algebra.Comparable as Comparable
import RoutingLib.Routing.VectorBased.Asynchronous as BellmanFord

open RawRoutingAlgebra hiding (_≟_)
open RawRoutingAlgebra A using ()
  renaming (_≈_ to _≈ᵃ_; _⊕_ to _⊕ᵃ_; _▷_ to _▷ᵃ_; 0# to 0#ᵃ; ∞# to ∞ᵃ)
open RawRoutingAlgebra B using ()
  renaming (_≈_ to _≈ᵇ_; _⊕_ to _⊕ᵇ_; _▷_ to _▷ᵇ_; 0# to 0#ᵇ; ∞# to ∞ᵇ)
open _Simulates_ A⇉B

private
  variable
    n : ℕ
    e : Epoch
    p : Subset n
    i : Fin n

--------------------------------------------------------------------------------
-- Proof

toNetwork : Network A n → Network B n
toNetwork N e i j = toₛ (N e i j)

fromNetwork : Network B n → Network A n
fromNetwork N e i j = fromₛ (N e i j)

module _ (Nᵇ : Network B n) where

  Nᵃ : Network A n
  Nᵃ = fromNetwork Nᵇ

  open BellmanFord A Nᵃ using (RoutingMatrix) renaming (F′ to Fᵃ; F∥ to F∥ᵃ; I to Iᵃ; Aₜ to Aᵃ)
  open BellmanFord B Nᵇ using () renaming (F′ to Fᵇ; F∥ to F∥ᵇ; I to Iᵇ; Aₜ to Aᵇ; F-cong to Fᵇ-cong)
  open Comparable A

  toIᵃ≈Iᵇ : ∀ i j → to (Iᵃ i j) ≈ᵇ Iᵇ i j
  toIᵃ≈Iᵇ i j with j ≟ i
  ... | yes _ = to-0#
  ... | no  _ = to-∞

  All-≎-tabulate : ∀ (X : RoutingMatrix) j → All (_≎ Iᵃ i j) (tabulate (λ k → Aᵃ e p i k ▷ᵃ X k j))
  All-≎-tabulate {i} {e} {p} X j with j ≟ i
  ... | yes _ = tabulate⁺ (λ k → e0# (Aᵃ e p i k) (X k j) (≈-refl A) (≈-refl A))
  ... | no  _ = tabulate⁺ (λ k → e∞# (Aᵃ e p i k) (X k j) (≈-refl A) (≈-refl A))

  AllPairs-≎-tabulate : ∀ (X : RoutingMatrix) j → AllPairs _≎_ (tabulate (λ k → Aᵃ e p i k ▷ᵃ X k j))
  AllPairs-≎-tabulate {e} {p} {i} X j = AllPairs.tabulate⁺ (λ i≢j → ee# (Aᵃ e p i _) (Aᵃ e p i _) (X _ j) (X _ j) i≢j (≈-refl A) (≈-refl A))

  toA : ∀ k → toₛ (Aᵃ e p i k) ≡ Aᵇ e p i k
  toA {e} {p} {i} k with i ∈? p | k ∈? p
  ... | no  _ | _     = to-f∞
  ... | yes _ | no  _ = to-f∞
  ... | yes _ | yes _ = toₛ-fromₛ (Nᵇ e i k)

  to-F : ∀ X j → to (Fᵃ e p X i j) ≈ᵇ Fᵇ e p (λ k l → to (X k l)) i j
  to-F {e} {p} {i} X j = begin
      to (Fᵃ e p X i j)
    ≡⟨⟩
      to (foldr _⊕ᵃ_ (Iᵃ i j) (tabulate (λ k → Aᵃ e p i k ▷ᵃ X k j)))
    ≈⟨ ≈-sym B (foldr-map-commute-gen₂ (S B) (⊕-cong B) ⊕-pres-≎ to-⊕ (All-≎-tabulate X j) (AllPairs-≎-tabulate X j)) ⟩
      foldr _⊕ᵇ_ (to (Iᵃ i j)) (map to (tabulate λ k → Aᵃ e p i k ▷ᵃ X k j))
    ≈⟨ foldr⁺ (S B) (⊕-cong B) (toIᵃ≈Iᵇ i j) (map-tabulate (S B) to (λ k → Aᵃ e p i k ▷ᵃ X k j)) ⟩
      foldr _⊕ᵇ_ (Iᵇ i j) (tabulate (λ k → to (Aᵃ e p i k ▷ᵃ X k j)))
    ≈⟨ foldr⁺ (S B) (⊕-cong B) (≈-refl B) (ListEq.tabulate⁺ (S B) (λ k → to-▷ (Aᵃ e p i k) (X k j)) ) ⟩
      foldr _⊕ᵇ_ (Iᵇ i j) (tabulate (λ k → toₛ (Aᵃ e p i k) ▷ᵇ to (X k j)))
    ≡⟨ cong (foldr _⊕ᵇ_ (Iᵇ i j)) (tabulate-cong {n = n} λ k → cong (_▷ᵇ _) (toA k) ) ⟩
      foldr _⊕ᵇ_ (Iᵇ i j) (tabulate (λ k → Aᵇ e p i k ▷ᵇ to (X k j)))
    ≡⟨⟩
      Fᵇ e p (λ k l → to (X k l)) i j
    ∎
    where open EqReasoning (S B)

  F∥ᵃ⇉F∥ᵇ : Async.Simulates F∥ᵃ F∥ᵇ
  F∥ᵃ⇉F∥ᵇ = record
    { toᵢ       = to ∘_
    ; fromᵢ     = from ∘_
    ; toᵢ-⊥     = toIᵃ≈Iᵇ _
    ; toᵢ-cong  = to-cong ∘_
    ; toᵢ-F     = to-F
    ; toᵢ-fromᵢ = to-from ∘_
    }

open BellmanFord using (F∥)

simulate : (∀ (N : Network A n) → Convergent (F∥ A N)) →
           (∀ (N : Network B n) → Convergent (F∥ B N))
simulate convergent Nᵇ = Async.simulate (F∥ᵃ⇉F∥ᵇ Nᵇ) (convergent (fromNetwork Nᵇ))
