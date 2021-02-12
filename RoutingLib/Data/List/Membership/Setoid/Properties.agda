open import Algebra using (Op₂; RightIdentity; Selective)
open import Data.Nat using (_≤_; _<_; zero; suc; s≤s; z≤n)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (suc-injective)
open import Data.List hiding (any)
open import Data.List.Relation.Unary.All using (All; _∷_; [])
open import Data.List.Relation.Unary.All.Properties using (All¬⇒¬Any)
open import Data.List.Relation.Unary.Unique.Setoid using (Unique; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
import Data.List.Membership.Setoid as Membership
open import Data.List.Membership.Setoid.Properties
open import Data.List.Relation.Binary.Pointwise as Pointwise using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there; any; index) renaming (map to mapₐ)
open import Data.Product using (∃; ∃₂; _×_; _,_; swap; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id)
open import Level using (Level)
open import Relation.Unary using (Decidable; _⇒_) renaming (_⊆_ to _⋐_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary
  using (Setoid; Rel; Symmetric; _Respects_; _Preserves_⟶_; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality
  using (refl; _≡_; _≢_; cong; subst; subst₂; inspect; [_])

open import RoutingLib.Data.List


module RoutingLib.Data.List.Membership.Setoid.Properties where

private
  variable
    a b c p ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    
-----------------------------------
-- Properties involving 1 setoid --
-----------------------------------

module _ (S : Setoid c ℓ) where

  open Setoid S renaming (Carrier to A; refl to ≈-refl)
  open Setoid (Pointwise.setoid S) using () renaming (_≈_ to _≈ₗ_; sym to symₗ; refl to reflₗ)

  open Membership S using (_∈_; _∉_)
  open Membership (Pointwise.setoid S) using () renaming (_∈_ to _∈ₗ_)

  index-cong : ∀ {x y xs} → (x∈xs : x ∈ xs) (y∈xs : y ∈ xs) → Unique S xs → x ≈ y → index x∈xs ≡ index y∈xs
  index-cong (here x≈z)   (here y≈z)   _            x≈y = refl
  index-cong (here x≈z)   (there y∈xs) (z≉xs ∷ xs!) x≈y = contradiction (∈-resp-≈ S (trans (sym x≈y) x≈z) y∈xs) (All¬⇒¬Any z≉xs)
  index-cong (there x∈xs) (here y≈z)   (z≉xs ∷ xs!) x≈y = contradiction (∈-resp-≈ S (trans x≈y y≈z) x∈xs) (All¬⇒¬Any z≉xs)
  index-cong (there x∈xs) (there y∈xs) (_ ∷ xs!)    x≈y = cong suc (index-cong x∈xs y∈xs xs! x≈y)

  index-injective : ∀ {xs} → Unique S xs → ∀ {x y} {x∈xs : x ∈ xs} {y∈xs : y ∈ xs} → index x∈xs ≡ index y∈xs → x ≈ y
  index-injective (_ ∷ _)   {x∈xs = here  x≈y}  {here  z≈y}  eq = trans x≈y (sym z≈y)
  index-injective (x ∷ xs!) {x∈xs = there x∈xs} {there y∈xs} eq = index-injective xs! {x∈xs = x∈xs} {y∈xs} (suc-injective eq)

  index-lookup : ∀ {xs} → Unique S xs → {i : Fin (length xs)} (xsᵢ∈xs : lookup xs i ∈ xs) → index xsᵢ∈xs ≡ i
  index-lookup (_    ∷ xs!) {zero}  (here px)      = refl
  index-lookup (x∉xs ∷ xs!) {suc i} (here  xsᵢ≈x)  = contradiction (∈-resp-≈ S xsᵢ≈x (∈-lookup S _ i)) (All¬⇒¬Any x∉xs)
  index-lookup (x∉xs ∷ xs!) {zero}  (there x∈xs)   = contradiction x∈xs (All¬⇒¬Any x∉xs)
  index-lookup (_    ∷ xs!) {suc i} (there xsᵢ∈xs) = cong suc (index-lookup xs! xsᵢ∈xs)
