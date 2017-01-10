open import Level using (_⊔_)
open import Data.Nat using (_≤_; _<_)
open import Relation.Binary using (Setoid)
open import Relation.Nullary using (¬_)

open import RoutingLib.Function.Metric

module RoutingLib.Function.Metric.Contraction 
    {a} {ℓ} {S : Setoid a ℓ} 
    (M : Metric S) 
    (f : Setoid.Carrier S → Setoid.Carrier S) 
    where

    open Setoid S
    open Metric M

    Contracting : Set a
    Contracting = ∀ x y → d (f x) (f y) ≤ d x y

    StrictlyContracting : Set (a ⊔ ℓ)
    StrictlyContracting = ∀ {x y} → ¬ (x ≈ y) → d (f x) (f y) < d x y

    ContractingOnOrbits : Set a
    ContractingOnOrbits = ∀ x → d (f x) (f (f x)) ≤ d x (f x)

    StrictlyContractingOnOrbits : Set (a ⊔ ℓ)
    StrictlyContractingOnOrbits = ∀ {x} → ¬ (x ≈ f x) → d (f x) (f (f x)) < d x (f x)

    c⇨cob : Contracting → ContractingOnOrbits
    c⇨cob c x = c x (f x)

    sc⇨scob : StrictlyContracting → StrictlyContractingOnOrbits
    sc⇨scob sc = sc
