module RoutingLib.Data.List.Relation.Unary.AllPairs where

open import Level using (_⊔_)
open import Data.List using (List; []; _∷_)
open import Data.List.All as All using (All; []; _∷_)
open import Data.Product using (_,_; _×_)
open import Relation.Binary using (Rel; _⇒_)
open import Relation.Unary using (_∩_; _⊆_)

data AllPairs {a ℓ} {A : Set a} (_~_ : Rel A ℓ) : List A → Set (a ⊔ ℓ) where
  []  : AllPairs _~_ []
  _∷_ : ∀ {x xs} → All (x ~_) xs → AllPairs _~_ xs → AllPairs _~_ (x ∷ xs)

zip : ∀ {a p q} {A : Set a} {_~₁_ : Rel A p} {_~₂_ : Rel A q} →
      AllPairs _~₁_ ∩ AllPairs _~₂_ ⊆ AllPairs (λ x y → x ~₁ y × x ~₂ y)
zip ([]          , [])          = []
zip (x~₁xs ∷ pxs , x~₂xs ∷ qxs) = All.zip (x~₁xs , x~₂xs) ∷ zip (pxs , qxs)

map : ∀ {a p q} {A : Set a} {_~₁_ : Rel A p} {_~₂_ : Rel A q} →
      _~₁_ ⇒ _~₂_ → AllPairs _~₁_ ⊆ AllPairs _~₂_
map ~₁⇒~₂ [] = []
map ~₁⇒~₂ (x~xs ∷ pxs) = All.map ~₁⇒~₂ x~xs ∷ (map ~₁⇒~₂ pxs)
