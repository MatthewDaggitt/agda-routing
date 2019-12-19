open import Data.Bool.Base using (true; false; not)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Fin.Properties as Finₚ
  using (_≤?_; <-cmp)
open import Data.List using ([]; _∷_; List; foldr; filter; map; tabulate)
import Data.List.Relation.Binary.Permutation.Setoid as PermutationEq
open import Data.Product.Relation.Lex.NonStrict using (×-decTotalOrder)
open import Data.Product.Relation.Pointwise.NonDependent using (×-decSetoid)
open import Data.Vec.Functional using (Vector)
open import Data.Vec.Functional.Relation.Binary.Pointwise.Properties using () renaming (setoid to Vec-setoid)
open import Function using (_∘_)
open import Level using (_⊔_)
open import Relation.Binary using (Rel; DecTotalOrder; Setoid; DecSetoid)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Nullary using (Dec; yes; no; ¬_; does; proof)
open import Relation.Nullary.Negation using (¬?; ¬-reflects)
open import Relation.Unary using (Pred; Decidable)
open import Algebra.FunctionProperties.Core
open import Data.Product as Prod using (_×_; _,_)

open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
import RoutingLib.Routing as Routing
import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra as RoutingAlgebra
import RoutingLib.Data.Vec.Functional.Relation.Binary.Equality as TableEquality
import RoutingLib.Data.List.Sorting.InsertionSort as InsertionSort

module RoutingLib.lmv34.Gamma_one.Algebra
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (n : ℕ) where

open Routing algebra n using (𝕋ₛ; RoutingMatrix; AdjacencyMatrix)
open RawRoutingAlgebra algebra
open RoutingAlgebra isRoutingAlgebra using (≤₊-decTotalOrder)

--------------------------------------------------------------------------------
-- Routing sets

RoutingSet : Set a
RoutingSet = List (Fin n × Route)

Ø : RoutingSet
Ø = []

-- RoutingVector setoid
FinRoute-decSetoid = ×-decSetoid (Finₚ.≡-decSetoid n) DS
open DecSetoid FinRoute-decSetoid public using () renaming (setoid to FinRoute-setoid)
open PermutationEq FinRoute-setoid public

--------------------------------------------------------------------------------
-- Routing vector

RoutingVector : Set a
RoutingVector = Vector RoutingSet n

Øᵥ : RoutingVector
Øᵥ i = Ø

𝕍ₛ : Setoid a (a ⊔ ℓ)
𝕍ₛ = Vec-setoid ↭-setoid n

open Setoid 𝕍ₛ public using ()
  renaming
  ( _≈_           to _≈ᵥ_
  ; reflexive     to ≈ᵥ-reflexive
  ; refl          to ≈ᵥ-refl
  ; sym           to ≈ᵥ-sym
  ; trans         to ≈ᵥ-trans
  ; isEquivalence to ≈ᵥ-isEquivalence
  )

--------------------------------------------------------------------------------
-- Auxilaries

-- MATTHEW: These definitions should really be the opposite way around to
-- avoid the double negative
IsValid : Pred (Fin n × Route) _
IsValid (d , v) = ¬ (v ≈ ∞#)

IsInvalid : Pred (Fin n × Route) _
IsInvalid p = ¬ (IsValid p)

IsValid? : Decidable IsValid
IsValid? (d , v) = ¬? (v ≟ ∞#)

decTotalOrder : DecTotalOrder a ℓ ℓ
decTotalOrder = ×-decTotalOrder (Finₚ.≤-decTotalOrder n) ≤₊-decTotalOrder

-- MATTHEW: If I were you I'd create a general version of this function
-- called `strictMerge` in `RoutingList.Data.List` and prove the properties
-- about it in general. You'll find it much easier going.
mergeSorted : Op₂ RoutingSet
mergeSorted [] ys = ys
mergeSorted (x ∷ xs) [] = x ∷ xs
mergeSorted ((d₁ , v₁) ∷ xs) ((d₂ , v₂) ∷ ys) with <-cmp d₁ d₂
... | tri< _ _ _ = (d₁ , v₁) ∷ (mergeSorted xs ((d₂ , v₂) ∷ ys))
... | tri> _ _ _ = (d₂ , v₂) ∷ (mergeSorted ((d₁ , v₁) ∷ xs) ys)
... | tri≈ _ _ _ = (d₁ , v₁ ⊕ v₂) ∷ (mergeSorted xs ys)

--------------------------------------------------------------------------------
-- Definitions

-- Remove invalid routes
infix 11 _†
_† : RoutingSet → RoutingSet
xs † = filter IsValid? xs

-- Set addition
infixl 10 _⊕ₛ_
_⊕ₛ_ : Op₂ RoutingSet
S₁ ⊕ₛ S₂ = mergeSorted (sort S₁) (sort S₂)
  where open InsertionSort decTotalOrder using (sort)

-- Vector addition
infixl 9 _⊕ᵥ_
_⊕ᵥ_ : Op₂ RoutingVector
(V₁ ⊕ᵥ V₂) i = (V₁ i) ⊕ₛ (V₂ i)

-- Big addition
infix 5 ⨁ₛ
⨁ₛ : ∀ {k} → (Fin k → RoutingSet) → RoutingSet
⨁ₛ iter = foldr _⊕ₛ_ Ø (tabulate iter)

-- Matrix to vector-of-sets transformation (Gamma_0 to Gamma_1)
infix 12 ~_
~_ : RoutingMatrix → RoutingVector
(~ M) i = (tabulate λ j → (j , M i j)) †

map₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} → (A → B) → List (C × A) → List (C × B)
map₂ f = map (Prod.map₂ f)

-- Function application to sets
infix 13 _[_]
_[_] : (Route → Route) → RoutingSet → RoutingSet
f [ X ] = (map₂ f X) †

-- Matrix application to vector-of-sets
infix 10 _〚_〛
_〚_〛 : AdjacencyMatrix → RoutingVector → RoutingVector
(A 〚 V 〛) i = ⨁ₛ (λ q → (A i q ▷_) [ V q ])
