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

import RoutingLib.Data.Table.Relation.DecidableEquality as TableDecEquality
import RoutingLib.Data.Matrix.Relation.DecidableEquality as MatrixDecEquality
import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.FiniteSubset.Equality as SubsetEquality
open import RoutingLib.Data.List.Relation.Pointwise using (foldr⁺)
open import RoutingLib.Data.List.Properties

open import RoutingLib.Iteration.Asynchronous.Dynamic
open import RoutingLib.Iteration.Asynchronous.Schedule using (Schedule; 𝕋; Epoch)

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.RoutingAlgebra
import RoutingLib.Routing.Algebra.RoutingAlgebra.Properties as RoutingAlgebraProperties
open import RoutingLib.Routing.Model as Model using (Network)
import RoutingLib.Routing.BellmanFord.Asynchronous as BellmanFord

module RoutingLib.Routing.BellmanFord.Asynchronous.DistanceVector.Properties
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  {n} (network : Network algebra n)
  where

open RawRoutingAlgebra algebra
open IsRoutingAlgebra isRoutingAlgebra
open RoutingAlgebraProperties isRoutingAlgebra

open BellmanFord algebra network

------------------------------------------------------------------------
-- Properties of σₜ

σₜ-cong' : ∀ e p {X Y} → X ≈ₘ[ p ] Y → σₜ e p X ≈ₘ σₜ e p Y
σₜ-cong' e p X≈Y _ j = foldr⁺ _≈_ ⊕-cong ≈-refl (tabulate⁺ (Aₜ-cong e p X≈Y))

σₜ-cong-∉ : ∀ e p {X Y} {i} → i ∉ p → σₜ e p X i ≈ₜ σₜ e p Y i
σₜ-cong-∉ e p {X} {Y} i∉p j = foldr⁺ _≈_ ⊕-cong ≈-refl (tabulate⁺ (λ k → Aₜ-reject-eq e _ k i∉p (X k j) (Y k j)))

σₜ-inactive : ∀ e {p} X → WellFormed p (σₜ e p X)
σₜ-inactive e {p} X {i} i∉p j with j ≟𝔽 i
... | yes j≡i = foldr-zeroʳ ⊕-magma ⊕-zeroʳ (tabulate λ k → Aₜ e p i k ▷ X k j)
... | no  j≢i = foldr-constant ⊕-magma (⊕-idem ∞) (All.tabulate⁺ (λ k → Aₜ-reject e i k (inj₁ i∉p) (X k j)))

------------------------------------------------------------------------
-- States in which the inactive nodes are actually inactive

X*-wf : ∀ e p {X*} → σₜ e p X* ≈ₘ X* → WellFormed p X*
X*-wf e p {X*} FX*≈X* {i} i∉p = ≈ₜ-trans (≈ₘ-sym FX*≈X* i) (σₜ-inactive e X* i∉p)
