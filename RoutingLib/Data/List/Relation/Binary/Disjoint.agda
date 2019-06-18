
open import Relation.Binary using (Setoid; Rel)

module RoutingLib.Data.List.Relation.Binary.Disjoint
  {c ℓ} (S : Setoid c ℓ) where

open import Level using (_⊔_)
open import Relation.Nullary using (¬_)
open import Function using (_∘_)
open import Data.List using (List; []; [_]; _∷_)
open import Data.List.Any using (here; there)
open import Data.Product using (_×_; _,_)

open Setoid S renaming (Carrier to A)
open import Data.List.Membership.Setoid S using (_∈_; _∉_)
open import Data.List.Relation.Binary.Disjoint.Setoid S

dropₗ : ∀ {x xs ys} → Disjoint (x ∷ xs) ys → Disjoint [ x ] ys
dropₗ x∷xs#ys (here v≈x , v∈ys) = x∷xs#ys (here v≈x , v∈ys)
dropₗ x∷xs#ys (there () , v∈ys)

∈ₗ⇒∉ᵣ : ∀ {xs ys} → Disjoint xs ys → ∀ {v} → v ∈ xs → v ∉ ys
∈ₗ⇒∉ᵣ xs#ys v∈xs v∈ys = xs#ys (v∈xs , v∈ys)
