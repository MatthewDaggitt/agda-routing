open import Level using (_⊔_)
open import Data.Vec hiding (zip)
open import Data.Vec.All using (All)
open import Data.Product using (uncurry)
open import Relation.Binary using (Rel)

open import RoutingLib.Data.Vec using (zip)

module RoutingLib.Data.Vec.All where

  data All₂ {a b p} {A : Set a} {B : Set b} (P : A → B → Set p) : ∀ {n} → Vec A n → Vec B n → Set (a ⊔ b ⊔ p) where
    []  : All₂ P [] []
    _∷_ : ∀ {n x y} {xs : Vec A n} {ys : Vec B n} → P x y → All₂ P xs ys → All₂ P (x ∷ xs) (y ∷ ys)

  data AllPairs {a ℓ} {A : Set a} (_~_ : Rel A ℓ) : ∀ {n} → Vec A n → Set (a ⊔ ℓ) where
    []  : AllPairs _~_ []
    _∷_ : ∀ {n x} {xs : Vec A n} → All (x ~_) xs → AllPairs _~_ xs → AllPairs _~_ (x ∷ xs)
