open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_)
open import Data.Nat.Properties using (≤-trans; m⊔n≤m+n)
open import Data.Product using (∃; _,_; proj₁; proj₂)
open import Relation.Binary using (Setoid; Decidable)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Data.Nat.Properties using (module ≤-Reasoning)

module RoutingLib.Function.Metric.Properties {a} {ℓ} (S : Setoid a ℓ) where

    open Setoid S renaming (Carrier to A)
    open import RoutingLib.Function.Metric S
    open import RoutingLib.Function.FixedPoint S

    -- Inequalities

    maxTriangle⇒triangle : ∀ {d} → MaxTriangleIneq d → TriangleIneq d
    maxTriangle⇒triangle {d} sti x y z = ≤-trans (sti x y z) (m⊔n≤m+n (d x y) (d y z))

    -- Contractions

    contr⇒contrOrbits : ∀ {d f} → f ContrOver d → f ContrOnOrbitsOver d
    contr⇒contrOrbits {_} {f} c x = c x (f x)

    strContr⇒strContrOrbits : ∀ {d f} → f StrContrOver d → f StrContrOnOrbitsOver d
    strContr⇒strContrOrbits sc = sc

{-
    strContr⇒strContrOnFP : ∀ {d f} → f StrContrOver d → f StrContrOnFixedPointOver d
    strContr⇒strContrOnFP {d} {f} sc {x*} {x} fx*≈x* x≉x* = begin
      d x*     (f x) ≡⟨ d-cong (sym fx*≈x*) (≈ₘ-refl {x = σ X}) ⟩
      d (f x*) (f x) <⟨ sc X≉X* ⟩
      d x*     x     ∎
      where open ≤-Reasoning
-}

    -- Balls

    ball-mono-≤ : ∀ {r s} → r ≤ s → ∀ d {x y} → x ∈[ d ∥ y , r ] → x ∈[ d ∥ y , s ]
    ball-mono-≤ r≤s d dxy≤r = ≤-trans dxy≤r r≤s

