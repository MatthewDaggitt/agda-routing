open import Level using (_⊔_)
open import Data.List using (List; []; _∷_) renaming (zipWith to zipWithₗ)
open import Data.List.All using (All; []; _∷_) renaming (map to all-map)
open import Data.Product using (_,_; _×_)
open import Relation.Binary using (Rel; REL; _⇒_)
open import Relation.Unary using (_∩_) renaming (_⊆_ to _⋐_)

module RoutingLib.Data.List.All where

  data AllPairs {a ℓ} {A : Set a} (_~_ : Rel A ℓ) : List A → Set (a ⊔ ℓ) where
    []  : AllPairs _~_ []
    _∷_ : ∀ {x xs} → All (x ~_) xs → AllPairs _~_ xs → AllPairs _~_ (x ∷ xs)

  all-product : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q} {xs} → All P xs → All Q xs → All (P ∩ Q) xs
  all-product [] [] = []
  all-product (px ∷ pxs) (qx ∷ qxs) = (px , qx) ∷ all-product pxs qxs

  allPairs-product : ∀ {a p q} {A : Set a} {_~₁_ : Rel A p} {_~₂_ : Rel A q} {xs} → AllPairs _~₁_ xs → AllPairs _~₂_ xs → AllPairs (λ x y → x ~₁ y × x ~₂ y) xs
  allPairs-product [] [] = []
  allPairs-product (x~₁xs ∷ pxs) (x~₂xs ∷ qxs) = all-product x~₁xs x~₂xs ∷ allPairs-product pxs qxs


  allPairs-map : ∀ {a p q} {A : Set a} {_~₁_ : Rel A p} {_~₂_ : Rel A q} → _~₁_ ⇒ _~₂_ → AllPairs _~₁_ ⋐ AllPairs _~₂_
  allPairs-map ~₁⇒~₂ [] = []
  allPairs-map ~₁⇒~₂ (x~xs ∷ pxs) = all-map ~₁⇒~₂ x~xs ∷ (allPairs-map ~₁⇒~₂ pxs)
