{-# OPTIONS --allow-unsolved-metas #-}

open import Algebra.FunctionProperties.Core using (Op₂)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; suc)
open import Data.List using (List; []; _∷_; all; filter)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary using (DecSetoid)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Decidable; Pred; ∁)

open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
import RoutingLib.lmv34.Gamma_one.Algebra as Gamma_one_Algebra
import RoutingLib.lmv34.Gamma_two.Algebra as Gamma_two_Algebra

module RoutingLib.lmv34.Gamma_three.Algebra
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (n : ℕ) where

open RawRoutingAlgebra algebra
open Gamma_one_Algebra isRoutingAlgebra n
open Gamma_two_Algebra isRoutingAlgebra n

open DecSetoid FinRoute-decSetoid renaming (_≟_ to _≟ᵣ_; _≈_ to _≈ᵣ_) 

-- Set subtraction
notContains : RoutingSet → Decidable _ 
notContains [] x = yes {!!}
notContains (y ∷ ys) x with x ≟ᵣ y
... | yes p = no {!!}
... | no p  = notContains ys x

_-_ : Op₂ RoutingSet
A - B = filter (notContains B) A

-- Set union
_∪_ : Op₂ RoutingSet
A ∪ B = {!!}

-- Set difference
diff : RoutingSet → RoutingSet → RoutingSet × RoutingSet
diff A B = (A - B , B - A)


_-ᵥ_ : Op₂ RoutingVector₂
(V -ᵥ V') i j = (V i j) - (V' i j)

_∪ᵥ_ : Op₂ RoutingVector₂
(V ∪ᵥ V') i j = (V i j) ∪ (V' i j)

diffᵥ : RoutingVector₂ → RoutingVector₂ → RoutingVector₂ × RoutingVector₂
proj₁ (diffᵥ V V') i j = proj₁ (diff (V i j) (V' i j))
proj₂ (diffᵥ V V') i j = proj₂ (diff (V i j) (V' i j))
