open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Fin.Properties as Finₚ
  using (_≤?_; <-cmp)
open import Data.List using ([]; _∷_; List; foldr; filter; map; tabulate)
import Data.List.Relation.Binary.Permutation.Setoid as PermutationEq
open import Data.Product.Relation.Lex.NonStrict using (×-decTotalOrder)
open import Data.Product.Relation.Pointwise.NonDependent using (×-decSetoid)
open import Relation.Binary using (Rel; DecTotalOrder; Setoid; DecSetoid)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Unary using (Pred; Decidable)
open import Algebra.FunctionProperties.Core
open import Data.Product using (_×_; _,_)

open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
import RoutingLib.Routing as Routing
import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra as RoutingAlgebra
open import Data.Vec.Functional using (Vector)
import RoutingLib.Data.Vec.Functional.Relation.Binary.Equality as TableEquality
import RoutingLib.Data.List.Sorting.InsertionSort as InsertionSort

module RoutingLib.lmv34.Gamma_one.Algebra
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (n : ℕ) where

open Routing algebra n using (RoutingMatrix; AdjacencyMatrix)
open RawRoutingAlgebra algebra
open RoutingAlgebra isRoutingAlgebra using (≤₊-decTotalOrder)

--------------------------------
-- Data
RoutingSet : Set a
RoutingSet = List (Fin n × Route)

Ø : RoutingSet
Ø = []

RoutingVector : Set a
RoutingVector = Vector RoutingSet n

Øᵥ : RoutingVector
Øᵥ i = Ø

-- RoutingVector setoid
FinRoute-decSetoid = ×-decSetoid (Finₚ.≡-decSetoid n) DS
open DecSetoid FinRoute-decSetoid public using () renaming (setoid to FinRoute-setoid)
open PermutationEq FinRoute-setoid public
open TableEquality ↭-setoid public using (𝕋ₛ) renaming
      ( _≈ₜ_             to _≈ᵥ_
      ; ≈ₜ-reflexive     to ≈ᵥ-reflexive
      ; ≈ₜ-refl          to ≈ᵥ-refl
      ; ≈ₜ-sym           to ≈ᵥ-sym
      ; ≈ₜ-trans         to ≈ᵥ-trans
      ; ≈ₜ-isEquivalence to ≈ᵥ-isEquivalence
      )
𝕍ₛ = 𝕋ₛ n

--------------------------------
-- Auxilaries

infix 11 _†
_† : RoutingSet → RoutingSet
xs † = filter (λ {(d , v) → ¬? (v ≟ ∞#)}) xs

decTotalOrder : DecTotalOrder a ℓ ℓ
decTotalOrder = ×-decTotalOrder (Finₚ.≤-decTotalOrder n) ≤₊-decTotalOrder

mergeSorted : Op₂ RoutingSet
mergeSorted [] ys = ys
mergeSorted (x ∷ xs) [] = x ∷ xs
mergeSorted ((d₁ , v₁) ∷ xs) ((d₂ , v₂) ∷ ys) with <-cmp d₁ d₂
... | tri< _ _ _ = (d₁ , v₁) ∷ (mergeSorted xs ((d₂ , v₂) ∷ ys))
... | tri> _ _ _ = (d₂ , v₂) ∷ (mergeSorted ((d₁ , v₁) ∷ xs) ys)
... | tri≈ _ _ _ = (d₁ , v₁ ⊕ v₂) ∷ (mergeSorted xs ys)

--------------------------------
-- Definitions

-- Set addition
infixl 10 _⊕ₛ_
_⊕ₛ_ : Op₂ RoutingSet
S₁ ⊕ₛ S₂ = mergeSorted (sort S₁) (sort S₂)
  where open InsertionSort decTotalOrder using (sort)

-- Vector addition
infixl 9 _⊕ᵥ_
_⊕ᵥ_ : Op₂ RoutingVector
(V₁ ⊕ᵥ V₂) i = V₁ i ⊕ₛ V₂ i

-- Big addition
infix 5 ⨁ₛ
⨁ₛ : ∀ {k} → (Fin k → RoutingSet) → RoutingSet
⨁ₛ iter = foldr _⊕ₛ_ Ø (tabulate iter)

-- Matrix to vector-of-sets transformation (Gamma_0 to Gamma_1)
infix 12 ~_
~_ : RoutingMatrix → RoutingVector
(~ M) i = (tabulate λ j → (j , M i j)) †

-- Function application to sets
infix 13 _[_]
_[_] : (Route → Route) → RoutingSet → RoutingSet
f [ X ] = (map (λ {(d , v) → (d , f v)}) X) †

toRouteMap : ∀ {i j : Fin n} → (f : Step i j) → Route → Route
toRouteMap f = λ s → f ▷ s

-- Matrix application to vector-of-sets
infix 10 _〚_〛
_〚_〛 : AdjacencyMatrix → RoutingVector → RoutingVector
(A 〚 V 〛) i = ⨁ₛ (λ q → (toRouteMap (A i q)) [ V q ])
