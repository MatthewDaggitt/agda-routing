open import Level using (_⊔_)
open import Data.Vec
open import Data.Vec.All using (All)
open import Relation.Binary using (Rel)

module RoutingLib.Data.Vec.All where

  data AllPairs {a ℓ} {A : Set a} (_~_ : Rel A ℓ) : ∀ {n} → Vec A n → Set (a ⊔ ℓ) where
    []  : AllPairs _~_ []
    _∷_ : ∀ {n x} {xs : Vec A n} → All (x ~_) xs → AllPairs _~_ xs → AllPairs _~_ (x ∷ xs)
