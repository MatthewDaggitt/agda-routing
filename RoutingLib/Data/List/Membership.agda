open import Relation.Binary using (Setoid; _Respects_; Decidable)
open import Data.List.Any as Any using (any)
open import Data.List using (List; []; _∷_)
open import Data.List.All using (All; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (yes; no)

module RoutingLib.Data.List.Membership {c ℓ} (S : Setoid c ℓ) where

  open Any.Membership S public hiding (∈-resp-≈)
  open Any public using (here; there)
  open Setoid S using (_≈_; sym) renaming (Carrier to A)



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
