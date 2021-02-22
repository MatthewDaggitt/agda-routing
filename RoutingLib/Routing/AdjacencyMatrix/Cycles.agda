
open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.AdjacencyMatrix.Cycles
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  where

open RawRoutingAlgebra algebra

open import RoutingLib.Routing algebra

open import Data.Bool using (true; false)
open import Data.Product using (∃₂; _,_)
open import Data.Fin.Base using (zero; suc; inject₁; toℕ)
open import Data.Fin.Properties as F using (any?; toℕ-inject₁)
open import Data.Fin.Patterns
open import Data.Nat using (s≤s; _<_)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Data.Nat.Properties using (≤-reflexive)
open import Data.Product using (_×_)
open import Level using (_⊔_)
open import Function.Base using (flip; _∘_)
open import Relation.Binary
open import Relation.Nullary using (¬_; does; Dec; yes; no)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Nullary.Negation using (¬?; contradiction)
import Relation.Unary as U
open import Relation.Binary.PropositionalEquality using (refl)

open import RoutingLib.Data.Fin using (_+ₘ_; _-ₘ_)
open import RoutingLib.Data.FiniteSet renaming (FiniteSet to FiniteSet⁺)

import RoutingLib.Routing.AdjacencyMatrix.Relations.Properties as AdjacencyMatrixProperties

--------------------------------------------------------------------------------
-- Definition

module _ {n} (A : AdjacencyMatrix n) where

  open import RoutingLib.Routing.AdjacencyMatrix.Relations algebra A
  
  -- A non-empty ordered finite set of routes X is cyclic if every route
  -- in the set threatens the adoption of the previous route in the set.
  Cyclic : FiniteSet⁺ Route → Set _
  Cyclic (⟦ _ ∣ X ⟧) = ∀ i → X (i -ₘ 1) ⊴ X i

  -- A topology/adjacency matrix, is cycle free if there exists no set of
  -- routes is cyclic.
  CycleFree : Set (a ⊔ ℓ)
  CycleFree = ∀ X → ¬ Cyclic X

--------------------------------------------------------------------------------
-- Properties


module _ (isRoutingAlgebra : IsRoutingAlgebra algebra) where

  open IsRoutingAlgebra isRoutingAlgebra
  open import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra isRoutingAlgebra

  Cyclic? : IsFinite algebra → ∀ {n} → Decidable (Cyclic {n})
  Cyclic? isFinite A (⟦ _ ∣ X ⟧) = F.all? λ i → ⊴-dec isFinite (X (i -ₘ 1)) (X i) 
    where open AdjacencyMatrixProperties isRoutingAlgebra A
