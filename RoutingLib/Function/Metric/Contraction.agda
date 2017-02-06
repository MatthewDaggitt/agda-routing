open import Level using (_⊔_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_;  _<′_)
open import Data.Nat.Properties using (≤⇒≤′)
open import Relation.Binary using (Setoid; Decidable; _Preserves_⟶_)
open import Relation.Binary.PropositionalEquality using (subst₂; cong) renaming (sym to ≡-sym)
open import Relation.Nullary using (¬_; yes; no)
open import Data.Product using (∃; _,_)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using (<-well-founded)

open import RoutingLib.Function using (_^_; ff^≡f^f)
open import RoutingLib.Function.Metric

module RoutingLib.Function.Metric.Contraction {a} {ℓ} (S : Setoid a ℓ) where

    open Setoid S renaming (Carrier to A)

    Contracting : (A → A → ℕ) → (A → A) → Set a
    Contracting d f = ∀ x y → d (f x) (f y) ≤ d x y

    StrictlyContracting : (A → A → ℕ) → (A → A) → Set (a ⊔ ℓ)
    StrictlyContracting d f = ∀ {x y} → ¬ (x ≈ y) → d (f x) (f y) < d x y

    ContractingOnOrbits : (A → A → ℕ) → (A → A) → Set a
    ContractingOnOrbits d f = ∀ x → d (f x) (f (f x)) ≤ d x (f x)

    StrictlyContractingOnOrbits : (A → A → ℕ) → (A → A) → Set (a ⊔ ℓ)
    StrictlyContractingOnOrbits d f = ∀ {x} → ¬ (x ≈ f x) → d (f x) (f (f x)) < d x (f x)

    c⇨cob : ∀ {d f} → Contracting d f → ContractingOnOrbits d f
    c⇨cob {_} {f} c x = c x (f x)

    sc⇨scob : ∀ {d f} → StrictlyContracting d f → StrictlyContractingOnOrbits d f
    sc⇨scob sc = sc


    -- If strictly contracting on orbits then we can find a fixed point

{-
    fixedPoint : Decidable _≈_ → StrictlyContractingOnOrbits → ∀ x → ∃ λ n → (f ^ n) x ≈ (f ^ (suc n)) x
    fixedPoint dec scob x = internal x (<-well-founded (d x (f x)))
      where
      internal : ∀ x → Acc _<′_ (d x (f x)) → ∃ λ n → (f ^ n) x ≈ (f ^ (suc n)) x
      internal x (acc t) with dec x (f x)
      ... | yes x≈fx = 0 , x≈fx
      ... | no  x≉fx with internal (f x) (t (d (f x) (f (f x))) (≤⇒≤′ (scob x≉fx)))
      ...   | (n , fⁿfx≈fⁿ⁺¹fx) = suc n , trans (trans (reflexive (ff^≡f^f f n x)) fⁿfx≈fⁿ⁺¹fx) (reflexive (≡-sym (ff^≡f^f f (suc n) x)))
-}
