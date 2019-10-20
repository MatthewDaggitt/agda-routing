open import Data.Maybe
open import Data.Maybe.Relation.Unary.Any hiding (drop-just)
open import Data.Maybe.Relation.Unary.All
open import Data.Unit using (tt)
open import Level
open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary.PropositionalEquality

module RoutingLib.Data.Maybe.Properties where

private
  variable
    a p : Level
    A : Set a
    P : Pred A p

IsJust? : (x : Maybe A) → Dec (Is-just x)
IsJust? (just x) = yes (just tt)
IsJust? nothing  = no  (λ())

IsNothing? : (x : Maybe A) → Dec (Is-nothing x)
IsNothing? (just x) = no λ { (just ())}
IsNothing? nothing  = yes nothing

All-witness : {P : Pred A p} → ∀ {x} → (jx : Is-just x) → All P x → P (to-witness jx)
All-witness (just x) = drop-just

to-witness-subst : ∀ {x} {v : A} (eq : x ≡ just v) → to-witness (subst Is-just (sym eq) (just {x = v} tt)) ≡ to-witness (just {x = v} tt)
to-witness-subst refl = refl

postulate All-witness′ : ∀ {P : Pred A p} {x : Maybe A} {v : A} →
                         (eq : x ≡ just v) → All P x → All P (just v)
