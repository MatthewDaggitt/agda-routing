
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Basics.Network as Routing using (Network)

module RoutingLib.Routing.VectorBased.Asynchronous.DistanceVector.Properties
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  {n} (N : Network algebra n)
  where

open RawRoutingAlgebra algebra
open IsRoutingAlgebra isRoutingAlgebra

open import Data.List using (tabulate)
open import Data.List.Relation.Binary.Pointwise using (tabulate⁺; foldr⁺)
import Data.List.Relation.Unary.All.Properties as All
open import Data.Fin using () renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Subset using (Subset; _∉_)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (_∈_)

open import RoutingLib.Data.List.Properties

open import RoutingLib.Routing.VectorBased.Asynchronous algebra N
 as CoreProperties
open import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra isRoutingAlgebra
open import RoutingLib.Routing.Basics.Network.Participants algebra hiding (Aₜ)

------------------------------------------------------------------------
-- Publicly re-export core properties

open import RoutingLib.Routing.VectorBased.Synchronous.DistanceVector.Properties
  isRoutingAlgebra public

------------------------------------------------------------------------
-- Properties of F′

F′-cong' : ∀ e p {X Y} → X ≈ₘ[ p ] Y → F′ e p X ≈ₘ F′ e p Y
F′-cong' e p X≈Y _ j = foldr⁺ {R = _≈_} ⊕-cong ≈-refl (tabulate⁺ (Aₜ-cong N e p X≈Y))

F′-cong-∉ : ∀ e p {X Y} {i} → i ∉ p → F′ e p X i ≈ₜ F′ e p Y i
F′-cong-∉ e p {X} {Y} i∉p j = foldr⁺ {R = _≈_} ⊕-cong ≈-refl (tabulate⁺ (λ k → Aₜ-reject-eq N e _ k i∉p (X k j) (Y k j)))

F′[X]∈Aₚ : ∀ e p X → F′ e p X ∈ Accordant p
F′[X]∈Aₚ e p X {i} i∉p j with j ≟𝔽 i
... | yes j≡i = foldr-zeroʳ    ⊕-magma ⊕-zeroʳ (tabulate λ k → Aₜ e p i k ▷ X k j)
... | no  j≢i = foldr-constant ⊕-magma (⊕-idem ∞#) (All.tabulate⁺ (λ k → Aₜ-reject N e i k (inj₁ i∉p) (X k j)))

F′-pres-Aₚ : ∀ {e p X} → X ∈ Accordant p → F′ e p X ∈ Accordant p
F′-pres-Aₚ {e} {p} {X} _ = F′[X]∈Aₚ e p X

------------------------------------------------------------------------
-- States in which the inactive nodes are actually inactive

X*∈Aₚ : ∀ e p {X*} → F′ e p X* ≈ₘ X* → X* ∈ Accordant p
X*∈Aₚ e p {X*} FX*≈X* {i} i∉p = ≈ₜ-trans (≈ₘ-sym FX*≈X* i) (F′[X]∈Aₚ e p X* i∉p)
