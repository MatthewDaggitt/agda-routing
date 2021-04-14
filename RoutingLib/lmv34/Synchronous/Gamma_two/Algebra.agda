open import Algebra.Core using (Op₂)
open import Relation.Binary using (Rel; Setoid)
open import Data.Fin using (Fin)
open import Data.List using (List; [])
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Level using (_⊔_) renaming (suc to lsuc)
open import Function.Base using (_∘_)

import RoutingLib.Routing as Routing
open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
open import RoutingLib.Data.Matrix using (SquareMatrix)

import RoutingLib.lmv34.Synchronous.Gamma_one.Algebra as Gamma_one_Algebra

module RoutingLib.lmv34.Synchronous.Gamma_two.Algebra
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (n : ℕ) where

open Routing algebra n using (RoutingMatrix; AdjacencyMatrix)
open RawRoutingAlgebra algebra
open Gamma_one_Algebra isRoutingAlgebra n

--------------------------
-- Data

RoutingVector₂ : Set a
RoutingVector₂ = SquareMatrix (List Assignment) n

Øᵥ,₂ : RoutingVector₂
Øᵥ,₂ i j = Ø

-- AdjacencyMatrixᵀ : Set b
-- AdjacencyMatrixᵀ = ∀ (i j : Fin n) → Step j i


-- tgg: New definition!
-- We need this, since the elements of Imp, Prot, and Exp are functions, not steps!
RouteMapMatrix : Set a
RouteMapMatrix = SquareMatrix (Route → Route) n

infix 10 _ᵀ
_ᵀ : RouteMapMatrix → RouteMapMatrix
(M ᵀ) i j = M j i

infix 10 _【_】
_【_】 : RouteMapMatrix → RoutingVector → RoutingVector₂
(F 【 V 】) i q = (F i q) [ V i ]

infix 10 _〖_〗
_〖_〗 : RouteMapMatrix → RoutingVector₂ → RoutingVector₂
(F 〖 O 〗) i q = (F i q) [ O q i ]

infix 11 _↓
_↓ : RoutingVector₂ → RoutingVector
(I ↓) i = ⨁ₛ (λ q → I i q) 

-- CompositionOp : Set b
-- CompositionOp = ∀ {i j : Fin n} → Op₂ (Step i j)

-- record IsCompositionOp (_●_ : CompositionOp) : Set (a ⊔ b ⊔ ℓ) where
--   field
--     isCompositionOp : ∀ {i j : Fin n} (f g : Step i j) (s : Route) → (f ● g) ▷ s ≈ f ▷ (g ▷ s)

infix 5 _≈ₐ,₂_
_≈ₐ,₂_ : RouteMapMatrix → RouteMapMatrix → Set (a ⊔ ℓ)
A ≈ₐ,₂ A' = ∀ i j s → (A i j) s ≈ (A' i j) s

-- module Composition
--  (_∘_ : CompositionOp) where
  
infix 12 _∘ₘ_
_∘ₘ_ : Op₂ RouteMapMatrix
(A ∘ₘ A') i j = (A i j) ∘ (A' i j)

-- need to coerce A to a RouteMapMatrix! 
toRouteMapMatrix : AdjacencyMatrix → RouteMapMatrix
toRouteMapMatrix A i j = A i j ▷_

IsComposition : AdjacencyMatrix → RouteMapMatrix → RouteMapMatrix → RouteMapMatrix → Set (a ⊔ ℓ)
IsComposition A Imp Prot Exp = (toRouteMapMatrix A) ≈ₐ,₂ ((Imp ∘ₘ Prot) ∘ₘ (Exp ᵀ))
