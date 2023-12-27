
module RoutingLib.Data.Maybe.Relation.Binary.Connected.Left where

open import Level
open import Data.Product
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Function
open import Relation.Binary hiding (_⇔_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec

import Data.Maybe.Relation.Binary.Connected as C

private
  variable
    a b ℓ : Level
    A : Set a
    B : Set b
    R S T : REL A B ℓ
    x y : A
    mz : Maybe A

------------------------------------------------------------------------
-- Definition

Connectedˡ : {A : Set a} {B : Set b} (R : REL A B ℓ) → REL A (Maybe B) (a ⊔ b ⊔ ℓ)
Connectedˡ R x y = C.Connected R (just x) y

open C public using (just) renaming (just-nothing to nothing)

------------------------------------------------------------------------
-- Properties

drop-just : Connectedˡ R x (just y) → R x y
drop-just = C.drop-just

just-equivalence : R x y ⇔ Connectedˡ R x (just y)
just-equivalence = mk⇔ just drop-just

------------------------------------------------------------------------
-- Relational properties

connectedˡ? : Decidable R → Decidable (Connectedˡ R)
connectedˡ? R? x = C.connected? R? (just x)
