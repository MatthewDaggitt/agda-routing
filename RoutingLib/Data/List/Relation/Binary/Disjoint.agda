open import Level using (_⊔_)
open import Relation.Binary using (Setoid; Rel)
open import Relation.Nullary using (¬_)
open import Function using (_∘_)
open import Data.List using (List; []; [_]; _∷_)
open import Data.List.Any using (here; there)
open import Data.Product using (_×_; _,_)

module RoutingLib.Data.List.Relation.Binary.Disjoint {c ℓ} (S : Setoid c ℓ) where

  open Setoid S renaming (Carrier to A)
  open import Data.List.Membership.Setoid S using (_∈_; _∉_)

  infix 4 _#_

  _#_ : Rel (List A) (ℓ ⊔ c)
  xs # ys = ∀ {v} → ¬ (v ∈ xs × v ∈ ys)

  contractₗ : ∀ {x xs ys} → (x ∷ xs) # ys → xs # ys
  contractₗ x∷xs∩ys=∅ (v∈xs , v∈ys) = x∷xs∩ys=∅ (there v∈xs , v∈ys)

  contractᵣ : ∀ {xs y ys} → xs # (y ∷ ys) → xs # ys
  contractᵣ xs#y∷ys (v∈xs , v∈ys) = xs#y∷ys (v∈xs , there v∈ys)

  dropₗ : ∀ {x xs ys} → (x ∷ xs) # ys → [ x ] # ys
  dropₗ x∷xs#ys (here v≈x , v∈ys) = x∷xs#ys (here v≈x , v∈ys)
  dropₗ x∷xs#ys (there () , v∈ys)

  ∈ₗ⇒∉ᵣ : ∀ {xs ys} → xs # ys → ∀ {v} → v ∈ xs → v ∉ ys
  ∈ₗ⇒∉ᵣ xs#ys v∈xs v∈ys = xs#ys (v∈xs , v∈ys)
