

module RoutingLib.Routing.Protocols.PathVector.ShortestWidestPaths where

open import Algebra.FunctionProperties using (Op₂)
{-
open import Data.Fin using (Fin)
open import Data.Maybe using (Maybe)
-- open import Data.Nat hiding (_≟_)
-- open import Data.Nat.Properties hiding (_≟_)
open import Relation.Binary
open import Relation.Nullary using (yes; no)

open import RoutingLib.Data.NatInf
open import RoutingLib.Data.NatInf.Properties
open import RoutingLib.Data.Path.Uncertified
open import RoutingLib.Algebra.Construct.Lexicographic using (Lex)
-}

open import Data.Product using (_×_; _,_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality


open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.Construct.AddPaths
  as AddPaths using (AddPaths)

open import RoutingLib.Routing.Protocols.DistanceVector.ShortestWidestPaths

Aˢʷᵖ : RawRoutingAlgebra 0ℓ 0ℓ 0ℓ
Aˢʷᵖ = AddPaths Aˢʷ

Aˢʷᵖ-isPathAlgebra : IsPathAlgebra Aˢʷᵖ
Aˢʷᵖ-isPathAlgebra = AddPaths.isPathAlgebra Aˢʷ


open PathDistributivity Aˢʷᵖ-isPathAlgebra
