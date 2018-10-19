open import Data.Product using (∃; _,_; proj₁; proj₂)
open import Data.Nat using (_<_)
open import Data.Nat.Properties using (<⇒≢)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using (<-well-founded)
open import Relation.Binary using (DecSetoid; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Function.Metric using (_StrContrOnOrbitsOver_; _StrContrOnFixedPointOver_)

module RoutingLib.Function.Metric.FixedPoint
  {a ℓ} (DS : DecSetoid a ℓ)
  d {f} (strContrOnOrbits : _StrContrOnOrbitsOver_ (DecSetoid.setoid DS) f d)
  where

open DecSetoid DS using (_≈_; _≟_; refl) renaming (Carrier to A; setoid to S)
open import RoutingLib.Function.FixedPoint S using (FixedPoint)

abstract

  fixedPoint : A → ∃ (λ x → FixedPoint f x)
  fixedPoint x = inner x (<-well-founded (d x (f x)))
    where
    inner : ∀ x → Acc _<_ (d x (f x)) → ∃ (λ x → FixedPoint f x)
    inner x (acc x-acc) with f x ≟ x
    ... | yes fx≈x = x , fx≈x
    ... | no  fx≉x = inner (f x) (x-acc (d (f x) (f (f x))) (strContrOnOrbits fx≉x))

  x* : A → A
  x* x = proj₁ (fixedPoint x)

  x*-fixed : ∀ x → f (x* x) ≈ x* x
  x*-fixed x = proj₂ (fixedPoint x)

  x*-unique : d Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_ → _StrContrOnFixedPointOver_ S f d → ∀ {x} v → f x ≈ x → x ≈ x* v
  x*-unique cong sfp {x} v fx≈x with x ≟ x* v
  ... | yes x≈x* = x≈x*
  ... | no  x≉x* = contradiction (cong refl fx≈x) (<⇒≢ (sfp (x*-fixed v) x≉x*))
