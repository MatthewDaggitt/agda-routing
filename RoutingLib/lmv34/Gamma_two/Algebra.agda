open import Algebra.FunctionProperties.Core using (Op₂)
open import Relation.Binary using (Rel; Setoid)
open import Data.Fin using (Fin)
open import Data.List using (List; [])
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
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

--------------------------
-- Data
RoutingVector₂ : Set a
RoutingVector₂ = SquareMatrix (List (Fin n × Route)) n

Øᵥ,₂ : RoutingVector₂
Øᵥ,₂ i j = []

-- RoutingVector₂ setoid
open MatrixEquality ↭-setoid public using (𝕄ₛ) renaming
       ( _≈ₘ_             to _≈ᵥ,₂_
       ; ≈ₘ-reflexive     to ≈ᵥ,₂-reflexive
       ; ≈ₘ-refl          to ≈ᵥ,₂-refl
       ; ≈ₘ-sym           to ≈ᵥ,₂-sym
       ; ≈ₘ-trans         to ≈ᵥ,₂-trans
       ; ≈ₘ-isEquivalence to ≈ᵥ,₂-isEquivalence
       )
𝕍₂ₛ = 𝕄ₛ n n

AdjacencyMatrixᵀ : Set b
AdjacencyMatrixᵀ = ∀ (i j : Fin n) → Step j i

infix 10 _ᵀ
_ᵀ : AdjacencyMatrixᵀ → AdjacencyMatrix
(M ᵀ) i j = M j i

infix 10 _【_】
_【_】 : AdjacencyMatrixᵀ → RoutingVector → RoutingVector₂
(F 【 V 】) i q = (F i q) [ V i ]

infix 10 _〖_〗
_〖_〗 : AdjacencyMatrix → RoutingVector₂ → RoutingVector₂
(F 〖 O 〗) i q = (F i q) [ O q i ]

infix 11 _↓
_↓ : RoutingVector₂ → RoutingVector
(I ↓) i = ⨁ₛ (λ q → I i q) 

IsComposition : (A ImpProt : AdjacencyMatrix) (Exp : AdjacencyMatrixᵀ) → Set (a ⊔ ℓ)
IsComposition A ImpProt Exp = ∀ {i j} → (s : Route) → (A i j) ▷ s ≈  (ImpProt i j) ▷ ((Exp j i) ▷ s) 
