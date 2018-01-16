open import Data.Nat using (ℕ; z≤n; s≤s; suc; ≤-pred) renaming (_<_ to _<ℕ_; _≤_ to _≤ℕ_)
open import Data.Nat.Properties using (≤+≢⇒<)
open import Data.Fin using (zero; suc) renaming (_≤_ to _≤𝔽_; _<_ to _<𝔽_)
open import Data.List using (_∷_; length)
open import Data.List.All as All using (All; []; _∷_)
open import Data.List.Any using (here; there)
open import Data.Product using (_,_; proj₁; proj₂; uncurry′)
open import Relation.Binary using (DecTotalOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; cong) renaming (setoid to ≡-setoid; refl to ≡-refl)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred)

open import RoutingLib.Data.List using (lookup)
open import RoutingLib.Data.List.All using (AllPairs; []; _∷_) using (allPairs-product; allPairs-map)
open import RoutingLib.Data.List.Uniqueness.Setoid using (Unique)
open import RoutingLib.Data.List.Uniqueness.Setoid.Properties using (perm!)
open import RoutingLib.Data.List.Permutation.Properties using (⇿-sym; ⇿-length)
open import RoutingLib.Data.List.Membership.Setoid.Properties using (∈-perm)
open import RoutingLib.Data.Nat.Properties using (≤⇒≯)

module RoutingLib.Data.List.Sorting.Properties {a ℓ₁ ℓ₂} (order : DecTotalOrder a ℓ₁ ℓ₂) where

  open DecTotalOrder order renaming (Carrier to A)
  open Eq using () renaming (setoid to S; trans to ≈-trans; sym to ≈-sym)
  
  open import RoutingLib.Data.List.Sorting order
  open import Data.List.Any.Membership S using (_∈_)
  open import Relation.Binary.NonStrictToStrict _≈_ _≤_ using (_<_) renaming (irrefl to <-irrefl)
  
  
  ↗-length : ∀ {xs ys} → xs ↗ ys → length xs ≡ length ys
  ↗-length (sorting xs⇿ys _) = ⇿-length xs⇿ys

  ↗-unique : ∀ {xs ys} → Unique S xs → xs ↗ ys → Unique S ys
  ↗-unique xs! (sorting xs⇿ys _) = perm! S xs! xs⇿ys

  ↗-∈ˡ : ∀ {x xs ys} → x ∈ xs → xs ↗ ys → x ∈ ys
  ↗-∈ˡ x∈xs (sorting xs⇿ys _) = ∈-perm S x∈xs xs⇿ys

  ↗-∈ʳ : ∀ {x xs ys} → x ∈ ys → xs ↗ ys → x ∈ xs
  ↗-∈ʳ x∈ys (sorting xs⇿ys _) = ∈-perm S x∈ys (⇿-sym xs⇿ys)

  postulate ↗-All : ∀ {p} {P : Pred A p} {xs ys} → xs ↗ ys → All P xs → All P ys
  





  postulate lookup-mono-≤ : ∀ {xs} → Sorted xs → ∀ {i j} → i ≤𝔽 j → lookup xs i ≤ lookup xs j
  
  postulate index-mono⁻¹-< : ∀ {xs} → Sorted xs → Unique S xs →
                           ∀ {i j} → lookup xs i < lookup xs j → i <𝔽 j
                           
  {-
  lookup-mono-≤ []         {()}
  lookup-mono-≤ (x↗ ∷ xs↗) {zero}  i≤j = All.lookup {!!} {!!}
  lookup-mono-≤ (x↗ ∷ xs↗) {suc i} i≤j = {!lookup-mono-0!}
  -}
{-
  ↗-indexOf-mono-< : ∀ {xs} → Sorted xs → ∀ {x y} (x∈xs : x ∈ xs) (y∈xs : y ∈ xs) → x < y → indexOf x∈xs <ℕ indexOf y∈xs
  ↗-indexOf-mono-< ↗xs          (here x≈z)   (here y≈z)  x<y          = contradiction x<y (<-irrefl (≈-trans x≈z (≈-sym y≈z)))
  ↗-indexOf-mono-< ↗xs          (here x≈z)    (there y∈xs) x<y         = s≤s z≤n
  ↗-indexOf-mono-< (z≤xs ∷ ↗xs) (there x∈xs) (here  y≈z)  (x≤y , x≉y) = contradiction (antisym x≤y (proj₂ ≤-resp-≈ (≈-sym y≈z) (lookupₐ (proj₁ ≤-resp-≈) z≤xs x∈xs))) x≉y
  ↗-indexOf-mono-< (_ ∷ ↗xs)    (there x∈xs) (there y∈xs) x<y         = s≤s (↗-indexOf-mono-< ↗xs x∈xs y∈xs x<y)
-}


{-

  indexOf-revMono-≤ _          (here x≈z)   (here y≈z)   _      = reflexive (≈-trans x≈z (≈-sym y≈z))
  indexOf-revMono-≤ (z≤xs ∷ _) (here x≈z)   (there y∈xs) _      = lookupₐ (proj₁ ≤-resp-≈) (mapₐ (proj₂ ≤-resp-≈ (≈-sym x≈z)) z≤xs) y∈xs
  index-revMono-≤ _          (there x∈xs) (here y≈z)   ()
  indexOf-revMono-≤ (_ ∷ ↗xs)  (there x∈xs) (there y∈xs) index≤ = ↗-indexOf-revMono-≤ ↗xs x∈xs y∈xs (≤-pred index≤)

  ↗-indexOf-⊤ : ∀ {xs} → Sorted xs → Unique S xs → ∀ {x} → (x∈xs : x ∈ xs) → All (_≤ x) xs → suc (indexOf x∈xs) ≡ length xs
  ↗-indexOf-⊤ (_         ∷ [])  _                      (here _)     (_ ∷ [])        = ≡-refl
  ↗-indexOf-⊤ ((z≤y ∷ _) ∷ _)   ((z≉y ∷ _) ∷ (_ ∷ _)) (here x≈z)   (_ ∷ (y≤x ∷ _)) = contradiction (antisym z≤y (proj₁ ≤-resp-≈ x≈z y≤x)) z≉y
  ↗-indexOf-⊤ (_         ∷ ↗xs) (_ ∷ xs!)             (there x∈xs) (_ ∷ xs≤x)       = cong suc (↗-indexOf-⊤ ↗xs xs! x∈xs xs≤x)
-}
