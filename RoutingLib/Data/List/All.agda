open import Level using (_⊔_)
open import Data.List using (List; []; _∷_)
open import Data.List.All using (All)
open import Relation.Binary using (Rel)

module RoutingLib.Data.List.All where

  data Chain {a p} {A : Set a} (P : Rel A p) : List A → Set (p ⊔ a) where
    [] : Chain P []
    [-] : ∀ {x} → Chain P (x ∷ [])
    _∷_ : ∀ {x y xs} → P x y → Chain P (y ∷ xs) → Chain P (x ∷ y ∷ xs)


  data AllPairs {a p} {A : Set a} (P : Rel A p) : List A → Set (p ⊔ a) where
    []  : AllPairs P []
    _∷_ : ∀ {x xs} → All (P x) xs → AllPairs P xs → AllPairs P (x ∷ xs)
