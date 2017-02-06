open import Data.Vec hiding (zip)
open import Data.Vec.All using (All)
open import Data.Product using (uncurry)

open import RoutingLib.Data.Vec using (zip)

module RoutingLib.Data.Vec.All where

  All₂ : ∀ {a b p} {A : Set a} {B : Set b} 
         (P : A → B → Set p) {k} → Vec A k → Vec B k → Set _
  All₂ P xs ys = All (uncurry P) (zip xs ys)
