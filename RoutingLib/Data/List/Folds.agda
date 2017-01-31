
open import Data.Product using (_,_; _×_; ∃)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; _∷_; []; foldr)
open import Data.List.All using (All; _∷_; [])
open import Data.List.Any using (Any; here; there; module Membership)
open import Relation.Binary using (Setoid)
open import Algebra.FunctionProperties using (Op₂)


open import RoutingLib.Algebra.FunctionProperties

module RoutingLib.Data.List.Folds where

  foldr-×preserves : ∀ {a p} {A : Set a} {P : A → Set p} {_•_} → _•_ ×-Preserves P → ∀ {e xs} → All P xs → P e → P (foldr _•_ e xs)
  foldr-×preserves _    []         pe = pe
  foldr-×preserves pres (px ∷ pxs) pe = pres px (foldr-×preserves pres pxs pe)

  foldr-forces× : ∀ {a p} {A : Set a} {P : A → Set p} {_•_} → _•_ Forces-× P → ∀ e xs → P (foldr _•_ e xs) → All P xs
  foldr-forces× _          _ []       _     = []
  foldr-forces× •-forces-P _ (x ∷ xs) Pfold with •-forces-P Pfold
  ... | (px , pfxs) = px ∷ foldr-forces× •-forces-P _ xs pfxs

  foldr-⊎preserves : ∀ {a p} {A : Set a} (P : A → Set p) {_•_} → _•_ ⊎-Preserves P → ∀ e xs → P e ⊎ Any P xs → P (foldr _•_ e xs)
  foldr-⊎preserves _ •-pres-P e []       (inj₁ Pe)          = Pe
  foldr-⊎preserves P •-pres-P e (_ ∷ xs) (inj₁ Pe)          = •-pres-P (inj₂ (foldr-⊎preserves P •-pres-P e xs (inj₁ Pe)))
  foldr-⊎preserves _ •-pres-P e []       (inj₂ ())
  foldr-⊎preserves _ •-pres-P e (_ ∷ xs) (inj₂ (here px))   = •-pres-P (inj₁ px)
  foldr-⊎preserves P •-pres-P e (_ ∷ xs) (inj₂ (there pxs)) = •-pres-P (inj₂ (foldr-⊎preserves P •-pres-P e xs (inj₂ pxs)))


{-
  module SetoidProperties {a ℓ} (S : Setoid a ℓ) where

    open import RoutingLib.Data.List.Any.GenericMembership S
    open Setoid S renaming (Carrier to A)

    foldr-⊎preserves' : ∀ {p} (P : A → Set p) {_•_} → Selective _≈_ _•_ → ∀ e xs
                        → (∀ {x y} → x ∈ xs → y ∈ xs → P x ⊎ P y → P (x • y))
                        → P e ⊎ Any P xs → P (foldr _•_ e xs)
    foldr-⊎preserves' _ sel e []       •-pres-P (inj₁ Pe)          = Pe
    foldr-⊎preserves' P sel e (_ ∷ xs) •-pres-P (inj₁ Pe)
      = •-pres-P (here refl) {!!} (inj₂ (foldr-⊎preserves' P sel e xs (λ x∈xs y∈xs → •-pres-P {!!} {!!}) (inj₁ Pe)))
    foldr-⊎preserves' _ sel e []       •-pres-P (inj₂ ())
    foldr-⊎preserves' _ sel e (_ ∷ xs) •-pres-P (inj₂ (here px))
      = •-pres-P (here refl) {!!} (inj₁ px)
    foldr-⊎preserves' P sel e (_ ∷ xs) •-pres-P (inj₂ (there pxs))
      = •-pres-P (here refl) {!!} (inj₂ (foldr-⊎preserves' P sel e xs (λ x∈xs y∈xs → •-pres-P (there x∈xs) (there y∈xs)) (inj₂ pxs)))
-}
