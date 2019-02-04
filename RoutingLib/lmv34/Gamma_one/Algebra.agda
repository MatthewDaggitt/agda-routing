{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.List using ([]; _∷_; List; foldr; filter; map; tabulate)
open import Function using (const)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (¬?)
open import Algebra.FunctionProperties.Core
open import Data.Product using (_×_; _,_)

open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra)
open import RoutingLib.Data.Table using (Table)
import RoutingLib.Routing as Routing

module RoutingLib.lmv34.Gamma_one.Algebra {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ) (n : ℕ) where

open Routing algebra n
open RawRoutingAlgebra algebra

--------------------------------
-- Data
RoutingVector : Set b
RoutingVector = Table (List (Fin n × Route)) n

--------------------------------

invalidSet : List (Fin n × Route)
invalidSet = tabulate (λ i → (i , ∞))

isValidRoute : (x : Route) → Dec (¬(x ≈ ∞))
isValidRoute x = ¬? (x ≟ ∞)

validRoutes : List (Fin n × Route) → List (Fin n × Route)
validRoutes xs = filter (λ {(d , v) → isValidRoute v}) xs

--------------------------------
-- Definitions

-- Set addition
infixl 10 _⊕ₛ_
_⊕ₛ_ : Op₂ (List (Fin n × Route))
S₁ ⊕ₛ S₂ = {!!}

-- Vector addition
infixl 9 _⊕ᵥ_
_⊕ᵥ_ : Op₂ RoutingVector
(V₁ ⊕ᵥ V₂) i = V₁ i ⊕ₛ V₂ i

-- Big choice operator
infix 5 ⨁ᵥ
⨁ᵥ : ∀ {k} → (Fin k → List (Fin n × Route)) → List (Fin n × Route)
⨁ᵥ iter = foldr _⊕ₛ_ invalidSet (tabulate iter)

-- Matrix to vector-of-sets transformation (Gamma_0 to Gamma_1)
infix 12 ~_
~_ : RoutingMatrix → RoutingVector
(~ M) i = validRoutes (tabulate λ j → (j , M i j))

-- Function application to sets
infix 13 _[_]
_[_] : ∀ {i j : Fin n} → (Step i j) → List (Fin n × Route) → List (Fin n × Route)
f [ X ] = validRoutes (map (λ {(d , v) → (d , f ▷ v)})  X)

-- Matrix application to vector-of-sets
infix 10 _〚_〛
_〚_〛 : AdjacencyMatrix → RoutingVector → RoutingVector
(A 〚 V 〛) i = ⨁ᵥ (λ q → (A i q) [ V q ])
