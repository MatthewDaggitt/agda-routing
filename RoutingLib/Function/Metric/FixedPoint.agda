open import Data.Product using (∃; _,_; proj₁; proj₂)
open import Data.Nat using (_<_)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using (<-well-founded)
open import Relation.Binary using (DecSetoid)
open import Relation.Nullary using (yes; no)

module RoutingLib.Function.Metric.FixedPoint {a ℓ} (DS : DecSetoid a ℓ) where

  open DecSetoid DS using (_≈_; _≟_) renaming (Carrier to A; setoid to S)
  open import RoutingLib.Function.Metric S using (_StrContrOnOrbitsOver_)
  open import RoutingLib.Function.FixedPoint S using (FixedPoint)

  module _ d {f} (strContrOnOrbits : f StrContrOnOrbitsOver d) where

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
