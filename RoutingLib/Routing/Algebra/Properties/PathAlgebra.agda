--------------------------------------------------------------------------------
-- Agda routing library
--
-- Properties of path algebras -- note that many more properties can be found
-- for certified path algebras.
--------------------------------------------------------------------------------

open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.Algebra.Properties.PathAlgebra
  {a b ℓ} {algebra  : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (isPathAlgebra : IsPathAlgebra algebra)
  where

open import Data.Fin using (toℕ)
open import Data.Maybe renaming (just to valid; nothing to invalid)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)
open import Function using (_∘_)
open import Level using (Lift; lift)
open import Relation.Binary.PropositionalEquality
  using (inspect; [_]; sym; module ≡-Reasoning)
import Relation.Binary.Reasoning.Setoid as EqReasoning
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Path.Uncertified
open import RoutingLib.Data.Path.Uncertified.Properties
import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra
  as RoutingAlgebraProperties

open RawRoutingAlgebra algebra
open IsPathAlgebra isPathAlgebra
open RoutingAlgebraProperties isRoutingAlgebra
open PathDistributivity isPathAlgebra

--------------------------------------------------------------------------------
-- Any path algebra that is increasing is also strictly increasing

incr⇒strIncr : IsIncreasing algebra → IsStrictlyIncreasing algebra
incr⇒strIncr incr {i = i} {k} f {x} x≉∞ with f ▷ x ≟ ∞#
... | yes fx≈∞ = ≈-sym (≈-trans (⊕-congʳ fx≈∞) (⊕-identityˡ x)) , x≉∞ ∘ (λ x≈fx → ≈-trans x≈fx fx≈∞)
... | no  fx≉∞ with path x | inspect path x
...   | invalid | [ p[x]≡∅ ] = contradiction (path[r]≈∅⇒r≈∞ p[x]≡∅) x≉∞
...   | valid p | [ p[x]≡p ] = incr f x , λ x≈fx → p≉i∷p (just-injective (begin
  valid p                      ≡⟨ sym p[x]≡p ⟩
  path x                       ≡⟨ path-cong x≈fx ⟩
  path (f ▷ x)                 ≡⟨ path-accept f p[x]≡p fx≉∞ ⟩
  valid ((toℕ i , toℕ k) ∷ p)  ∎))
  where open ≡-Reasoning


--------------------------------------------------------------------------------
-- kᵗʰ-level distributivity properties

isLevelPDistrib-cong : ∀ k {w x y z} → w ≈ x → y ≈ z →
                       IsLevel k PathDistributiveIn[ w , y ]Alt →
                       IsLevel k PathDistributiveIn[ x , z ]Alt
isLevelPDistrib-cong zero    w≈x y≈z (lift x≈z) = lift (≈-trans (≈-trans (≈-sym w≈x) x≈z) y≈z)
isLevelPDistrib-cong (suc k) w≈x y≈z distrib f x≤u u≤z x≤v v≤z i∉px i∉pz ij⇿px ij⇿pz =
  (distrib f
    (≤₊-respˡ-≈ (≈-sym w≈x) x≤u)
    (≤₊-respʳ-≈ (≈-sym y≈z) u≤z)
    (≤₊-respˡ-≈ (≈-sym w≈x) x≤v)
    (≤₊-respʳ-≈ (≈-sym y≈z) v≤z)
    i∉px
    i∉pz
    ij⇿px
    ij⇿pz)

isLevelPDistrib-equal : ∀ k {x y} → x ≈ y → IsLevel k PathDistributiveIn[ x , y ]Alt
isLevelPDistrib-equal zero    {_} {_} x≈y = lift x≈y
isLevelPDistrib-equal (suc k) {x} {y} x≈y f {u} {v} x≤u u≤y x≤v v≤y _ _ _ _ =
  isLevelPDistrib-equal k (begin
    f ▷ (u ⊕ v)       ≈⟨ ▷-cong f (⊕-congˡ (≈-sym u≈v)) ⟩
    f ▷ (u ⊕ u)       ≈⟨ ▷-cong f (⊕-idem u) ⟩
    f ▷ u             ≈⟨ ≈-sym (⊕-idem (f ▷ u)) ⟩
    (f ▷ u) ⊕ (f ▷ u) ≈⟨ ⊕-congˡ (▷-cong f u≈v) ⟩
    (f ▷ u) ⊕ (f ▷ v) ∎)
    where
    open EqReasoning S
    u≈v : u ≈ v
    u≈v = begin
      u  ≈⟨ ≤₊-antisym (≤₊-respʳ-≈ (≈-sym x≈y) u≤y) x≤u ⟩
      x  ≈⟨ ≤₊-antisym x≤v (≤₊-respʳ-≈ (≈-sym x≈y) v≤y) ⟩
      v  ∎
