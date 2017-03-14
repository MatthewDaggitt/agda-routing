open import Level using (_⊔_)
open import Data.Vec hiding (zip)
open import Data.Vec.All using (All)
open import Data.Product using (uncurry)

open import RoutingLib.Data.Vec using (zip)

module RoutingLib.Data.Vec.All where

  data All₂ {a b p} {A : Set a} {B : Set b} (P : A → B → Set p) : ∀ {n} → Vec A n → Vec B n → Set (a ⊔ b ⊔ p) where
    []  : All₂ P [] []
    _∷_ : ∀ {n x y} {xs : Vec A n} {ys : Vec B n} → P x y → All₂ P xs ys → All₂ P (x ∷ xs) (y ∷ ys)
