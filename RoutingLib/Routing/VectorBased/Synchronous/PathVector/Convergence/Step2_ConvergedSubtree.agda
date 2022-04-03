open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; _∈_; _∉_; _∪_; Nonempty)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Nat using (ℕ; NonZero; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Unit using ()
open import Data.Empty using (⊥)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using (List)
open import Data.List.Relation.Unary.All using (lookup)
import Data.List.Extrema as Extrema
open import Relation.Unary using () renaming (_∈_ to _∈ᵤ_; _∉_ to _∉ᵤ_)
import Relation.Binary.Reasoning.PartialOrder as POR
open import Relation.Binary.PropositionalEquality
  using (refl; _≢_; subst)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Matrix using (SquareMatrix)
open import RoutingLib.Data.Fin.Subset using (Nonfull)
open import RoutingLib.Data.Fin.Subset.Properties using (Nonfull-witness)
open import RoutingLib.Data.Fin.Subset.Cutset
open import RoutingLib.Data.List using (allFinPairs)
open import RoutingLib.Routing.Basics.Path.CertifiedI.AllVertices
open import RoutingLib.Routing.Basics.Path.CertifiedI.Properties
import RoutingLib.Function.Reasoning as FunctionalReasoning

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Prelude using (RoutingMatrix; AdjacencyMatrix)
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.Convergence.Prelude as Prelude
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.Convergence.Step1_NodeSets as Step1_NodeSets

module RoutingLib.Routing.VectorBased.Synchronous.PathVector.Convergence.Step2_ConvergedSubtree
  {a b ℓ n-1} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra    : IsRoutingAlgebra algebra)
  (isPathAlgebra       : IsCertifiedPathAlgebra algebra (suc n-1))
  (A : AdjacencyMatrix algebra (suc n-1))
  (X : RoutingMatrix   algebra (suc n-1))
  (j : Fin (suc n-1))
  (open Prelude isRoutingAlgebra isPathAlgebra A)
  (open Step1_NodeSets isRoutingAlgebra isPathAlgebra A X j)
  (t : ℕ)
  (C : Subset n)
  (C-nonFull : Nonfull C)
  (j∈C : j ∈ C)
  where

open Notation X j
open Extrema ≤₊-totalOrder

------------------------------------------------------------------------------
-- Finding the fixed minimal edge entering the fixed set

abstract

  private
    -- At least one edge entering the fixed set exists
    eₐ : Edge
    eₐ = proj₁ (Nonfull-witness C-nonFull) , j

    eₐ↷C : eₐ ↷ C
    eₐ↷C = proj₂ (Nonfull-witness C-nonFull) , j∈C

  -- We can therefore find the minimum weight edge out of the fixed set
  eₘᵢₙ : Edge
  eₘᵢₙ = argmin (weightₑ t) eₐ (cutset C)

  eₘᵢₙ↷C : eₘᵢₙ ↷ C
  eₘᵢₙ↷C = argmin-all (weightₑ t) eₐ↷C (∈cutset⇒↷ C)

  c↷C⇒eₘᵢₙ≤ₜe : ∀ {e} → e ↷ C → weightₑ t eₘᵢₙ ≤₊ weightₑ t e
  c↷C⇒eₘᵢₙ≤ₜe e↷C = lookup (f[argmin]≤f[xs] eₐ (cutset C)) (↷⇒∈cutset e↷C)
  
iₘᵢₙ : Node
iₘᵢₙ = proj₁ eₘᵢₙ

kₘᵢₙ : Node
kₘᵢₙ = proj₂ eₘᵢₙ

iₘᵢₙ∉C : iₘᵢₙ ∉ C
iₘᵢₙ∉C = proj₁ eₘᵢₙ↷C

kₘᵢₙ∈C : kₘᵢₙ ∈ C
kₘᵢₙ∈C = proj₂ eₘᵢₙ↷C

j≢iₘᵢₙ : j ≢ iₘᵢₙ
j≢iₘᵢₙ j≡iₘᵢₙ = iₘᵢₙ∉C (subst (_∈ C) j≡iₘᵢₙ j∈C)


