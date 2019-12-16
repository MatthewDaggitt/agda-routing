open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.Algebra.Consequences
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  where

open RawRoutingAlgebra algebra
open IsRoutingAlgebra isRoutingAlgebra

open import Data.Product using (proj₁)
open import Data.Nat using (suc)
open import Level using (lift)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.Reasoning.Setoid S

open import RoutingLib.Routing algebra
open import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra isRoutingAlgebra

--------------------------------------------------------------------------------
-- If the algebra is strictly increasing it's also increasing

strIncr⇒incr : IsStrictlyIncreasing algebra → IsIncreasing algebra
strIncr⇒incr strIncr f x with x ≟ ∞#
... | no  x≉∞ = proj₁ (strIncr f x≉∞)
... | yes x≈∞ = ≈-sym (begin
  (f ▷ x)  ⊕ x  ≈⟨ ⊕-cong (▷-cong f x≈∞) x≈∞ ⟩
  (f ▷ ∞#) ⊕ ∞# ≈⟨ ⊕-congʳ (▷-fixedPoint f) ⟩
  ∞#       ⊕ ∞# ≈⟨ ⊕-idem ∞# ⟩
  ∞#            ≈⟨ ≈-sym x≈∞ ⟩
  x             ∎)

--------------------------------------------------------------------------------
-- If the algebra is strictly increasing all networks are cycle-free

{-
strIncr⇒∄cyclic : IsStrictlyIncreasing algebra →
                  ∀ {n} (A : AdjacencyMatrix n) X → (∀ i → FiniteSet⁺.x X i ≉ ∞#) → ¬ Cyclic _ A X
strIncr⇒∄cyclic strInc A ⟦ zero  ∣ X ⟧ Xᵢ≉∞ cyclic with cyclic zero
... | (k , j , AₖⱼX₀≤X₀) = ≤₊⇒≯₊ AₖⱼX₀≤X₀ (strInc (A k j) (Xᵢ≉∞ zero))
strIncr⇒∄cyclic strInc A ⟦ suc n ∣ X ⟧ Xᵢ≉∞ cyclic =
  strIncr⇒∄cyclic strInc A ⟦ n ∣ X ∘ suc ⟧ (Xᵢ≉∞ ∘ suc) (λ
    { zero    → {!!} , {!!} , {!!}
    ; (suc i) → {!!}
    })


-- If the algebra is strictly increasing then every topology is cycle-free
strIncr⇒cycleFree : IsStrictlyIncreasing algebra →
                    ∀ {n} (A : AdjacencyMatrix n) → CycleFree _ A
strIncr⇒cycleFree strIncr A {X} Xᵢ≉∞ cyclic = strIncr⇒∄cyclic strIncr A {!!} cyclic
-}
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
