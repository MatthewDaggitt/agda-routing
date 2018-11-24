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

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.CertifiedPathAlgebra
open import RoutingLib.Routing as Routing using (AdjacencyMatrix)
import RoutingLib.Routing.VectorBased.Asynchronous as VectorBased
import RoutingLib.Routing.VectorBased.Asynchronous.DistanceVector.Properties as DistanceVectorProperties
import RoutingLib.Routing.VectorBased.Core.PathProperties as CorePathProperties

module RoutingLib.Routing.VectorBased.Asynchronous.PathVector.Properties
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n} (isCertifiedPathAlgebra : IsCertifiedPathAlgebra algebra n)
  (A : AdjacencyMatrix algebra n)
  where

open IsCertifiedPathAlgebra isCertifiedPathAlgebra

------------------------------------------------------------------------
-- Publicly re-export core properties

open DistanceVectorProperties isRoutingAlgebra public
open CorePathProperties isCertifiedPathAlgebra A public

