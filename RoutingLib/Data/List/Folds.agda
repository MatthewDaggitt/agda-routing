
open import Data.Product using (_,_; _×_; ∃)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; _∷_; []; foldr)
open import Data.List.All using (All; _∷_; [])
open import Data.List.Any using (here; there; module Membership)
open import Relation.Binary using (Setoid)
open import Algebra.FunctionProperties using (Op₂)


open import RoutingLib.Algebra.FunctionProperties

module RoutingLib.Data.List.Folds where

  module _ {a ℓ} (S : Setoid a ℓ) where
 
    open Setoid S renaming (Carrier to A)
    open Membership S using (_∈_)
    open import RoutingLib.Data.List.Any.GenericMembership S using (∈-resp-≈)

    foldr-⊎preserves : ∀ {p} {P : A → Set p} {_•_} → _•_ ⊎-Preserves P → (∀ {x y} → x ≈ y → P x → P y) → ∀ e xs → (P e ⊎ ∃ λ v → v ∈ xs × P v) → P (foldr _•_ e xs)
    foldr-⊎preserves pres _    _ []       (inj₁ pe)                    = pe
    foldr-⊎preserves pres cong e (x ∷ xs) (inj₁ pe)                    = pres (inj₂ (foldr-⊎preserves pres cong e xs (inj₁ pe)))
    foldr-⊎preserves pres cong _ []       (inj₂ (_ , ()         , _))
    foldr-⊎preserves pres cong e (x ∷ xs) (inj₂ (v , here  v≈x  , Pv)) = pres (inj₁ (cong v≈x Pv))
    foldr-⊎preserves pres cong e (x ∷ xs) (inj₂ (v , there v∈xs , Pv)) = pres (inj₂ (foldr-⊎preserves pres cong e xs (inj₂ (v , v∈xs , Pv))))

  foldr-×preserves : ∀ {a p} {A : Set a} {P : A → Set p} {_•_} → _•_ ×-Preserves P → ∀ {e xs} → All P xs → P e → P (foldr _•_ e xs)
  foldr-×preserves _    []         pe = pe
  foldr-×preserves pres (px ∷ pxs) pe = pres px (foldr-×preserves pres pxs pe)

  foldr-forces× : ∀ {a p} {A : Set a} {P : A → Set p} {_•_} → _•_ Forces-× P → ∀ e xs → P (foldr _•_ e xs) → All P xs
  foldr-forces× _          _ []       _     = []
  foldr-forces× •-forces-P _ (x ∷ xs) Pfold with •-forces-P Pfold
  ... | (px , pfxs) = px ∷ foldr-forces× •-forces-P _ xs pfxs

  
