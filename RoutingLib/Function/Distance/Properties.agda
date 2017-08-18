open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_)
open import Data.Nat.Properties using (≤-trans; m⊔n≤m+n)
open import Data.Product using (∃; _,_; proj₁; proj₂)
open import Relation.Binary using (Setoid; Decidable)
open import Relation.Nullary using (yes; no)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using (<-well-founded)

module RoutingLib.Function.Distance.Properties {a} {ℓ} (S : Setoid a ℓ) where

    open Setoid S renaming (Carrier to A)
    open import RoutingLib.Function.Distance S
    open import RoutingLib.Function.FixedPoint S
    
    -- Inequalities
    
    maxTriangle⇒triangle : ∀ {d} → MaxTriangleIneq d → TriangleIneq d
    maxTriangle⇒triangle {d} sti x y z = ≤-trans (sti x y z) (m⊔n≤m+n (d x y) (d y z))
  
    -- Contractions
    
    contr⇒contrOnOrbits : ∀ {d f} → f ContrOver d → f ContrOnOrbitsOver d
    contr⇒contrOnOrbits {_} {f} c x = c x (f x)

    strContr⇒strContrOnOrbits : ∀ {d f} → f StrContrOver d → f StrContrOnOrbitsOver d
    strContr⇒strContrOnOrbits sc = sc

    -- Balls

    ball-mono-≤ : ∀ {r s} → r ≤ s → ∀ d {x y} → x ∈[ d ∥ y , r ] → x ∈[ d ∥ y , s ]
    ball-mono-≤ r≤s d dxy≤r = ≤-trans dxy≤r r≤s


    -- Convergence

    module _ (_≟_ : Decidable _≈_) d {f} (strContrOnOrbits : f StrContrOnOrbitsOver d) where

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
