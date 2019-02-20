open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (_≤?_; <-cmp) renaming (_≟_ to _≟₁_; ≤-decTotalOrder to fin-decTotalOrder; setoid to Fin-setoid)
open import Data.List using ([]; _∷_; List; foldr; filter; map; tabulate)
open import Data.Product.Relation.Lex.NonStrict using (×-decTotalOrder)
open import Data.Product.Relation.Pointwise.NonDependent using (_×ₛ_)
open import Function using (const)
open import Relation.Binary using (Rel; DecTotalOrder; Setoid)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.Core using (tri<; tri≈; tri>)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Unary using (Pred; Decidable)
open import Algebra.FunctionProperties.Core
open import Data.Product using (_×_; _,_)

open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
import RoutingLib.Routing as Routing
import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra as RoutingAlgebra
open import RoutingLib.Data.Table using (Table)
import RoutingLib.Data.Table.Relation.Equality as TableEquality
import RoutingLib.Data.List.Sorting.InsertionSort as InsertionSort
import RoutingLib.Data.List.Relation.Permutation.Setoid as PermutationEq

module RoutingLib.lmv34.Gamma_one.Algebra
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (n : ℕ) where

open Routing algebra n using (RoutingMatrix; AdjacencyMatrix)
open RawRoutingAlgebra algebra
open RoutingAlgebra isRoutingAlgebra using (≤₊-decTotalOrder)

--------------------------------
-- Data
RoutingVector : Set b
RoutingVector = Table (List (Fin n × Route)) n

-- RoutingVector setoid
×-setoid = Fin-setoid n ×ₛ S
open PermutationEq ×-setoid using (↭-setoid)
open TableEquality ↭-setoid public using (𝕋ₛ) renaming
      ( _≈ₜ_             to _≈ᵥ_
      ; ≈ₜ-reflexive     to ≈ᵥ-reflexive
      ; ≈ₜ-refl          to ≈ᵥ-refl
      ; ≈ₜ-sym           to ≈ᵥ-sym
      ; ≈ₜ-trans         to ≈ᵥ-trans
      ; ≈ₜ-isEquivalence to ≈ᵥ-isEquivalence
      )
𝕍ₛ = 𝕋ₛ n
open EqReasoning 𝕍ₛ public
    using (begin_ ; _∎ ; _≡⟨⟩_; _≡⟨_⟩_)
    renaming (_≈⟨_⟩_ to _≈ᵥ⟨_⟩_)

--------------------------------

invalidSet : List (Fin n × Route)
invalidSet = []

isValidRoute : (x : Route) → Dec (¬(x ≈ ∞))
isValidRoute x = ¬? (x ≟ ∞)

validRoutes : List (Fin n × Route) → List (Fin n × Route)
validRoutes xs = filter (λ {(d , v) → isValidRoute v}) xs

decTotalOrder : DecTotalOrder b ℓ ℓ
decTotalOrder = ×-decTotalOrder (fin-decTotalOrder n) ≤₊-decTotalOrder

open InsertionSort decTotalOrder using (sort)

mergeSorted : Op₂ (List (Fin n × Route))
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
_⊕ₛ_ : Op₂ (List (Fin n × Route))
S₁ ⊕ₛ S₂ = mergeSorted (sort S₁) (sort S₂)

-- Vector addition
infixl 9 _⊕ᵥ_
_⊕ᵥ_ : Op₂ RoutingVector
(V₁ ⊕ᵥ V₂) i = V₁ i ⊕ₛ V₂ i

-- Big addition
infix 5 ⨁ₛ
⨁ₛ : ∀ {k} → (Fin k → List (Fin n × Route)) → List (Fin n × Route)
⨁ₛ iter = foldr _⊕ₛ_ invalidSet (tabulate iter)

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
(A 〚 V 〛) i = ⨁ₛ (λ q → (A i q) [ V q ])
