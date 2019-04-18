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
open import Data.Product using (_,_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (inspect; [_]; sym; module ≡-Reasoning)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Path.Uncertified
open import RoutingLib.Data.Path.Uncertified.Properties
import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra
  as RoutingAlgebraProperties

open RawRoutingAlgebra algebra
open IsPathAlgebra isPathAlgebra
open RoutingAlgebraProperties isRoutingAlgebra

--------------------------------------------------------------------------------
-- Any path algebra that is increasing is also strictly increasing

incr⇒strIncr : IsIncreasing algebra → IsStrictlyIncreasing algebra
incr⇒strIncr incr {i = i} {k} f {x} x≉∞ with f ▷ x ≟ ∞#
... | yes fx≈∞ = ≈-trans (⊕-cong fx≈∞ ≈-refl) (⊕-identityˡ x) , x≉∞ ∘ (λ x≈fx → ≈-trans x≈fx fx≈∞)
... | no  fx≉∞ with path x | inspect path x
...   | invalid | [ p[x]≡∅ ] = contradiction (path[r]≈∅⇒r≈∞ p[x]≡∅) x≉∞
...   | valid p | [ p[x]≡p ] = incr f x , λ x≈fx → p≉i∷p (just-injective (begin
  valid p                      ≡⟨ sym p[x]≡p ⟩
  path x                       ≡⟨ path-cong x≈fx ⟩
  path (f ▷ x)                 ≡⟨ path-accept f p[x]≡p fx≉∞ ⟩
  valid ((toℕ i , toℕ k) ∷ p)  ∎))
  where open ≡-Reasoning
