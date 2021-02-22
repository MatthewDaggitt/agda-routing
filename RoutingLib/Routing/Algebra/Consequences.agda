open import Data.Bool using (true; false)
open import Data.Fin.Base using (zero; suc; inject₁; toℕ)
open import Data.Fin.Properties as F using (any?; toℕ-inject₁)
open import Data.Fin.Patterns
open import Data.Fin.Subset using (Subset)
open import Data.Nat using (suc; s≤s; _<_)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Data.Nat.Properties using (≤-reflexive)
open import Data.Product using (_×_; ∃₂; _,_; proj₁)
open import Level using (_⊔_; lift)
open import Function.Base using (flip; _∘_)
open import Relation.Binary using ()
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_; does; Dec; yes; no)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Nullary.Negation using (¬?; contradiction)
open import Relation.Unary using (Universal)

open import RoutingLib.Data.Fin using (_+ₘ_; _-ₘ_)
open import RoutingLib.Data.FiniteSet renaming (FiniteSet to FiniteSet⁺)

open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.AdjacencyMatrix.Relations.Properties as AdjacencyMatrixProperties

module RoutingLib.Routing.Algebra.Consequences
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  where

open RawRoutingAlgebra algebra
open IsRoutingAlgebra isRoutingAlgebra

open import RoutingLib.Routing algebra
open import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra isRoutingAlgebra
open import RoutingLib.Routing.AdjacencyMatrix.Cycles algebra
open import RoutingLib.Routing.Network.Definitions algebra
open import Relation.Binary.Reasoning.PartialOrder ≤₊-poset

--------------------------------------------------------------------------------
-- If the algebra is strictly increasing it's also increasing

strIncr⇒incr : IsStrictlyIncreasing algebra → IsIncreasing algebra
strIncr⇒incr strIncr f x with x ≟ ∞#
... | no  x≉∞ = proj₁ (strIncr f x≉∞)
... | yes x≈∞ = ≈-sym (begin-equality
  (f ▷ x)  ⊕ x  ≈⟨ ⊕-cong (▷-cong f x≈∞) x≈∞ ⟩
  (f ▷ ∞#) ⊕ ∞# ≈⟨ ⊕-congʳ (▷-fixedPoint f) ⟩
  ∞#       ⊕ ∞# ≈⟨ ⊕-idem ∞# ⟩
  ∞#            ≈⟨ ≈-sym x≈∞ ⟩
  x             ∎)

--------------------------------------------------------------------------------
-- Relationship between strictly increasing algebras and cycle-free topologies

-- If the algebra is strictly increasing then all adjacency matrices are
-- guaranteed to be cycle free

strIncr⇒allCycleFree : IsStrictlyIncreasing algebra →
                       ∀ {n} (A : AdjacencyMatrix n) → CycleFree A
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

------------------------------------------------------------------------
-- Free networks

-- If the algebra is strictly increasing, then any network is free for
-- every epoch and set of participants

strIncr⇒free : IsStrictlyIncreasing algebra →
               ∀ {n} (N : Network n) → Universal (TopologyIsFree N)
strIncr⇒free strIncr N (e , p) = strIncr⇒allCycleFree strIncr (Aₜ N e p)

--------------------------------------------------------------------------------
-- kᵗʰ-level distributivity properties
{-
isLevelDistrib-shrink : ∀ k {w x y z} → w ≤₊ x → x ≤₊ z → z ≤₊ y →
                        Level_DistributiveIn[_,_]Alt algebra k w y →
                        Level_DistributiveIn[_,_]Alt algebra k x z
isLevelDistrib-shrink zero    w≤x x≤z z≤y (lift w≈y) = lift (≤₊-antisym x≤z (≤₊-trans z≤y (≤₊-respˡ-≈ w≈y w≤x)))
isLevelDistrib-shrink (suc k) {w} {x} {y} {z} w≤x _ z≤y distrib f x≤u u≤z x≤v v≤z =
  (distrib f
    (≤₊-trans w≤x x≤u)
    (≤₊-trans u≤z z≤y)
    (≤₊-trans w≤x x≤v)
    (≤₊-trans v≤z z≤y))

isLevelDistrib-equal : ∀ k {x y} → x ≈ y → Level_DistributiveIn[_,_]Alt algebra k x y 
isLevelDistrib-equal zero    {_} {_} x≈y = lift x≈y
isLevelDistrib-equal (suc k) {x} {y} x≈y f {u} {v} x≤u u≤y x≤v v≤y =
  isLevelDistrib-equal k (begin
    f ▷ (u ⊕ v)       ≈⟨ ▷-cong f (⊕-congˡ (≈-sym u≈v)) ⟩
    f ▷ (u ⊕ u)       ≈⟨ ▷-cong f (⊕-idem u) ⟩
    f ▷ u             ≈⟨ ≈-sym (⊕-idem (f ▷ u)) ⟩
    (f ▷ u) ⊕ (f ▷ u) ≈⟨ ⊕-congˡ (▷-cong f u≈v) ⟩
    (f ▷ u) ⊕ (f ▷ v) ∎)
    where
    u≈v : u ≈ v
    u≈v = begin
      u  ≈⟨ ≤₊-antisym (≤₊-respʳ-≈ (≈-sym x≈y) u≤y) x≤u ⟩
      x  ≈⟨ ≤₊-antisym x≤v (≤₊-respʳ-≈ (≈-sym x≈y) v≤y) ⟩
      v  ∎
-}
