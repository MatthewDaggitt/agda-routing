open import Relation.Binary using (DecTotalOrder)

module RoutingLib.Data.List.Sorting.Properties {a ℓ₁ ℓ₂} (order : DecTotalOrder a ℓ₁ ℓ₂) where

open import Data.Nat using (ℕ; z≤n; s≤s; suc; ≤-pred) renaming (_<_ to _<ℕ_; _≤_ to _≤ℕ_)
open import Data.Nat.Properties using (≤+≢⇒<; ≤⇒≯)
open import Data.Fin using (zero; suc) renaming (_≤_ to _≤𝔽_; _<_ to _<𝔽_)
open import Data.List using ([]; _∷_; length; lookup)
open import Data.List.All as All using (All; []; _∷_)
open import Data.List.Any using (here; there; index)
open import Data.List.Membership.Setoid.Properties using (∈-lookup)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂; uncurry′)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong) renaming (setoid to ≡-setoid; refl to ≡-refl)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred)

open import RoutingLib.Data.List using (insert)
open import RoutingLib.Data.List.Relation.Unary.All.Properties as Allₚ

open DecTotalOrder order renaming (Carrier to A)
open Eq using () renaming (setoid to S; trans to ≈-trans; sym to ≈-sym)

open import RoutingLib.Data.List.Sorting _≤_
open import Data.List.Membership.Setoid S using (_∈_)
open import Relation.Binary.Construct.NonStrictToStrict _≈_ _≤_ using (_<_) renaming (irrefl to <-irrefl)

  {-
  ↗-length : ∀ {xs ys} → xs ↗ ys → length xs ≡ length ys
  ↗-length (sorting xs⇿ys _) = ⇿-length xs⇿ys

  ↗-unique : ∀ {xs ys} → Unique S xs → xs ↗ ys → Unique S ys
  ↗-unique xs! (sorting xs⇿ys _) = perm! S xs! xs⇿ys

  ↗-∈ˡ : ∀ {x xs ys} → x ∈ xs → xs ↗ ys → x ∈ ys
  ↗-∈ˡ x∈xs (sorting xs⇿ys _) = ∈-perm S x∈xs xs⇿ys

  ↗-∈ʳ : ∀ {x xs ys} → x ∈ ys → xs ↗ ys → x ∈ xs
  ↗-∈ʳ x∈ys (sorting xs⇿ys _) = ∈-perm S x∈ys (⇿-sym xs⇿ys)
  -}

private

  lemma : ∀ {x y xs} → All (x ≤_) xs → y ∈ xs → x ≤ y
  lemma [] ()
  lemma (px ∷ xs) (here  x≈z)  = proj₁ ≤-resp-≈ (≈-sym x≈z) px
  lemma (px ∷ xs) (there y∈xs) = lemma xs y∈xs

lookup-mono-≤ : ∀ {xs} → Sorted xs → ∀ {i j} → i ≤𝔽 j → lookup xs i ≤ lookup xs j
lookup-mono-≤ {[]}     xs↗ {()}
lookup-mono-≤ {x ∷ xs} (x≤xs ∷ xs↗) {zero}  {zero}  z≤n = refl
lookup-mono-≤ {x ∷ xs} (x≤xs ∷ xs↗) {zero}  {suc j} z≤n = lemma x≤xs (∈-lookup S xs j)
lookup-mono-≤ {x ∷ xs} (x≤xs ∷ xs↗) {suc i} {zero}  ()
lookup-mono-≤ {x ∷ xs} (x≤xs ∷ xs↗) {suc i} {suc j} (s≤s i≤j) = lookup-mono-≤ xs↗ i≤j

index-mono-< : ∀ {xs} → Sorted xs → ∀ {x y} (x∈xs : x ∈ xs) (y∈xs : y ∈ xs) →
               x < y → index x∈xs <𝔽 index y∈xs
index-mono-< []           ()
index-mono-< (x≤xs ∷ xs↗) (here x≈z)   (here y≈z) (x≤y , x≉y) = contradiction (≈-trans x≈z (≈-sym y≈z)) x≉y
index-mono-< (x≤xs ∷ xs↗) (here x≈z)   (there y∈xs) (x≤y , x≉y) = s≤s z≤n
index-mono-< (x≤xs ∷ xs↗) (there x∈xs) (here y≈z)    (x≤y , x≉y) = contradiction (antisym x≤y (proj₂ ≤-resp-≈ (≈-sym y≈z) (lemma x≤xs x∈xs))) x≉y
index-mono-< (x≤xs ∷ xs↗) (there x∈xs) (there y∈xs) x<y = s≤s (index-mono-< xs↗ x∈xs y∈xs x<y)



------------------------------------------------------------------------

insert↗⁺ : ∀ v {xs} → Sorted xs → Sorted (insert total v xs)
insert↗⁺ v {_}      []           = [] ∷ []
insert↗⁺ v {x ∷ xs} (x≤xs ∷ xs↗) with total v x
... | inj₁ v≤x = (v≤x ∷ All.map (trans v≤x) x≤xs) ∷ x≤xs ∷ xs↗
... | inj₂ x≤v = (Allₚ.insert⁺ total x≤v x≤xs) ∷ insert↗⁺ v xs↗
