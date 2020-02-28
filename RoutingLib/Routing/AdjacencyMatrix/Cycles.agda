
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
open import Relation.Nullary using (¬_; does; yes; no)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Nullary.Negation using (¬?; contradiction)
open import Relation.Binary.PropositionalEquality using (refl)

open import RoutingLib.Data.Fin using (_+ₘ_; _-ₘ_)
open import RoutingLib.Data.FiniteSet renaming (FiniteSet to FiniteSet⁺)

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
  open import Relation.Binary.Reasoning.PartialOrder ≤₊-poset
  import RoutingLib.Routing.AdjacencyMatrix.Relations.Properties as AdjacencyMatrixProperties

  -- If the algebra is strictly increasing then all adjacency matrices are
  -- guaranteed to be cycle free

  strIncr⇒allCycleFree : IsStrictlyIncreasing algebra →
                         (∀ {n} (A : AdjacencyMatrix n) → CycleFree A)
  strIncr⇒allCycleFree strIncr A X cyclic = <₊-irrefl ≈-refl x₀<x₀
    where
    open AdjacencyMatrixProperties isRoutingAlgebra A

    x₋₁<x₀ : last X <₊ first X 
    x₋₁<x₀ = strIncr∧⊴⇒<₊ strIncr (cyclic 0F)

    v≤x₀⇒v≤xᵢ : ∀ {v} → v ≤₊ first X → ∀ {i} → Acc _<_ (toℕ i) → v ≤₊ iᵗʰ X i
    v≤x₀⇒v≤xᵢ {v} v≤X₀ {zero}  _         = v≤X₀
    v≤x₀⇒v≤xᵢ {v} v≤X₀ {suc i} (acc rec) = begin
      v                 ≤⟨ v≤x₀⇒v≤xᵢ v≤X₀ (rec (toℕ (inject₁ i)) (s≤s (≤-reflexive (toℕ-inject₁ i)))) ⟩
      iᵗʰ X (inject₁ i) <⟨ strIncr∧⊴⇒<₊ strIncr (cyclic (suc i)) ⟩
      iᵗʰ X (suc i)     ∎

    x₀<x₀ : first X <₊ first X
    x₀<x₀ = ≤-<₊-trans (v≤x₀⇒v≤xᵢ ≤₊-refl (<-wellFounded _)) x₋₁<x₀

  -- Conversely if all adjacency matrices are cycle free then the
  -- algebra is necessarily strictly increasing.

  allCycleFree⇒strIncr : (∀ {n} (A : AdjacencyMatrix n) → CycleFree A) →
                         IsStrictlyIncreasing algebra
  allCycleFree⇒strIncr cycleFree {n} {i} {j} f {x} x≉∞ with f ▷ x ≤₊? x
  ... | no  fx≰x = ≰₊⇒>₊ fx≰x
  ... | yes fx≤x = contradiction X-cyclic (cycleFree Aₓ X)
    where
    Aₓ : AdjacencyMatrix n
    Aₓ k l with k F.≟ i | l F.≟ j
    ... | yes refl | yes refl = f
    ... | _        | _        = f∞ k l

    Aₓᵢⱼ▷x≈f▷x : Aₓ i j ▷ x ≈ f ▷ x
    Aₓᵢⱼ▷x≈f▷x with i F.≟ i | j F.≟ j
    ... | yes refl | yes refl = ≈-refl
    ... | no  i≢i  | _        = contradiction refl i≢i
    ... | _        | no j≢j   = contradiction refl j≢j

    X : FiniteSet⁺ Route
    X = ⟦ 0 ∣ (λ {0F → x}) ⟧

    X-cyclic : Cyclic Aₓ X
    X-cyclic 0F = f ▷ x , (x≉∞ , i , j , Aₓᵢⱼ▷x≈f▷x) , fx≤x
