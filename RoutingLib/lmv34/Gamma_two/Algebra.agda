open import Algebra.FunctionProperties.Core using (Op₂)
open import Relation.Binary using (Rel)
open import Data.Fin using (Fin)
open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Function using (_∘_)
open import Level using (_⊔_) renaming (suc to lsuc)

import RoutingLib.Routing as Routing
open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
open import RoutingLib.Data.Matrix using (SquareMatrix)
import RoutingLib.Data.Matrix.Relation.Equality as MatrixEquality
import RoutingLib.lmv34.Gamma_one.Algebra as Gamma_one_Algebra

module RoutingLib.lmv34.Gamma_two.Algebra
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (n : ℕ) where

open Routing algebra n using (RoutingMatrix; AdjacencyMatrix)
open RawRoutingAlgebra algebra
open Gamma_one_Algebra isRoutingAlgebra n
open MatrixEquality ↭-setoid using (_≈ₘ_)

RoutingVector₂ : Set b
RoutingVector₂ = SquareMatrix (List (Fin n × Route)) n

infix 10 _【_】
_【_】 : AdjacencyMatrix → RoutingVector → RoutingVector₂
(F 【 V 】) i q = (F i q) [ V i ]

infix 10 _〖_〗
_〖_〗 : AdjacencyMatrix → RoutingVector₂ → RoutingVector₂
(F 〖 O 〗) i q = (F i q) [ O q i ]

infix 11 _↓
_↓ : RoutingVector₂ → RoutingVector
(I ↓) i = ⨁ₛ (λ q → I i q) 

IsComposition : (A Imp Prot Exp : AdjacencyMatrix) (V : RoutingVector) → Set (b ⊔ ℓ)
IsComposition A Imp Prot Exp V = (A 【 V 】) ≈ₘ  (Imp 〖 Prot 〖 Exp 【 V 】 〗 〗) 
