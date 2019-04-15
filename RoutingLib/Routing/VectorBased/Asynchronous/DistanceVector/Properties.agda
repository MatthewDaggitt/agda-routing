open import Data.List using (tabulate)
open import Data.List.Relation.Pointwise using (tabulate⁺)
import Data.List.All.Properties as All
open import Data.Fin using () renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Dec using (_∈?_)
open import Data.Fin.Subset using (Subset; _∉_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Indexed.Homogeneous using (IndexedDecSetoid)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

import RoutingLib.Data.Table.Relation.Binary.DecidableEquality as TableDecEquality
import RoutingLib.Data.Matrix.Relation.Binary.DecidableEquality as MatrixDecEquality
import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.FiniteSubset.Equality as SubsetEquality
open import RoutingLib.Data.List.Relation.Binary.Pointwise using (foldr⁺)
open import RoutingLib.Data.List.Properties

open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra as RoutingAlgebraProperties
open import RoutingLib.Routing as Routing using (Network)
import RoutingLib.Routing.VectorBased.Asynchronous as VectorBased
import RoutingLib.Routing.VectorBased.Core.Properties as CoreProperties

module RoutingLib.Routing.VectorBased.Asynchronous.DistanceVector.Properties
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  {n} (network : Network algebra n)
  where

open RawRoutingAlgebra algebra
open IsRoutingAlgebra isRoutingAlgebra
open RoutingAlgebraProperties isRoutingAlgebra

open VectorBased algebra network

------------------------------------------------------------------------
-- Publicly re-export core properties

open CoreProperties isRoutingAlgebra public

------------------------------------------------------------------------
-- Properties of F′

F′-cong' : ∀ e p {X Y} → X ≈ₘ[ p ] Y → F′ e p X ≈ₘ F′ e p Y
F′-cong' e p X≈Y _ j = foldr⁺ _≈_ ⊕-cong ≈-refl (tabulate⁺ (Aₜ-cong network e p X≈Y))

F′-cong-∉ : ∀ e p {X Y} {i} → i ∉ p → F′ e p X i ≈ₜ F′ e p Y i
F′-cong-∉ e p {X} {Y} i∉p j = foldr⁺ _≈_ ⊕-cong ≈-refl (tabulate⁺ (λ k → Aₜ-reject-eq network e _ k i∉p (X k j) (Y k j)))

F′-inactive : ∀ e p X → WellFormed p (F′ e p X)
F′-inactive e p X {i} i∉p j with j ≟𝔽 i
... | yes j≡i = foldr-zeroʳ ⊕-magma ⊕-zeroʳ (tabulate λ k → Aₜ e p i k ▷ X k j)
... | no  j≢i = foldr-constant ⊕-magma (⊕-idem ∞#) (All.tabulate⁺ (λ k → Aₜ-reject network e i k (inj₁ i∉p) (X k j)))

------------------------------------------------------------------------
-- States in which the inactive nodes are actually inactive

X*-wf : ∀ e p {X*} → F′ e p X* ≈ₘ X* → WellFormed p X*
X*-wf e p {X*} FX*≈X* {i} i∉p = ≈ₜ-trans (≈ₘ-sym FX*≈X* i) (F′-inactive e p X* i∉p)
