open import Relation.Binary using (Setoid; _Respects_; Decidable)
open import Data.List.Any using (any; here; there)
open import Data.List using (List; []; _∷_)
open import Data.List.All using (All; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (yes; no)

module RoutingLib.Data.List.Any.Membership {c ℓ} (S : Setoid c ℓ) where

  open Setoid S using (_≈_; sym) renaming (Carrier to A)
  open import Data.List.Any.Membership S using (_∈_)

  indexOf : ∀ {x xs} → x ∈ xs → ℕ
  indexOf (here px)    = zero
  indexOf (there x∈xs) = suc (indexOf x∈xs)

  lookupₐ : ∀ {p} {P : A → Set p} {xs} → P Respects _≈_ → All P xs → ∀ {x} → x ∈ xs → P x
  lookupₐ resp (pz ∷ pxs) (here  x≈z)  = resp (sym x≈z) pz
  lookupₐ resp (pz ∷ pxs) (there x∈xs) = lookupₐ resp pxs x∈xs

  deduplicate : Decidable _≈_ → List A → List A
  deduplicate _≟_ []       = []
  deduplicate _≟_ (x ∷ xs) with any (x ≟_) xs
  ... | yes _ = deduplicate _≟_ xs
  ... | no  _ = x ∷ (deduplicate _≟_ xs)
