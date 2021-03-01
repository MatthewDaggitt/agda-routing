
module RoutingLib.Data.Vec.Functional.Relation.Binary.Pointwise where

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (all?)
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Pointwise
open import Data.Vec.Functional.Relation.Binary.Pointwise.Properties
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary as B
  using (Setoid; DecSetoid; IsEquivalence; IsDecEquivalence; REL; Rel)
open import Relation.Binary.Indexed.Homogeneous hiding (REL; Rel)
open import Relation.Binary.PropositionalEquality
  using (_≡_) renaming (refl to ≡-refl)
open import Function using (_∘_)
open import Algebra.Core using (Op₂)

open import RoutingLib.Data.Vec.Functional


------------------------------------------------------------------------------
-- Relational properties

module _ {a ℓ} {A : Set a} {_~_ : Rel A ℓ} where

  reflexive : _≡_ B.⇒ _~_ → ∀ {n} → _≡_ B.⇒ Pointwise _~_ {n}
  reflexive reflexive ≡-refl i = reflexive ≡-refl

  isIndexedEquivalence : IsEquivalence _~_ → IsIndexedEquivalence (Vector A) (Pointwise _~_)
  isIndexedEquivalence isEq = record
    { reflᵢ  = refl  {R = _~_} Eq.refl
    ; symᵢ   = sym   {R = _~_} Eq.sym
    ; transᵢ = trans {R = _~_} Eq.trans
    } where module Eq = IsEquivalence isEq

------------------------------------------------------------------------------
-- foldr

module _ where

  foldr⁺-cong : ∀ {a b ℓ} {A : Set a} {B : Set b} {_~_ : REL A B ℓ}
                {_•_ : Op₂ A} {_◦_ : Op₂ B} →
                (∀ {w x y z} → w ~ x → y ~ z → (w • y) ~ (x ◦ z)) →
                ∀ {n} {s : Vector A (suc n)} {t : Vector B (suc n)} →
                Pointwise _~_ s t → foldr⁺ _•_ s ~ foldr⁺ _◦_ t
  foldr⁺-cong •◦-cong {zero}  s~t = s~t zero
  foldr⁺-cong •◦-cong {suc n} s~t = •◦-cong (s~t zero) (foldr⁺-cong (λ {w x y z} → •◦-cong {w} {x} {y} {z}) (s~t ∘ suc))
