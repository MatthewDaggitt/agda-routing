open import Relation.Binary using (Total; Setoid; Rel; Reflexive; Symmetric; Transitive; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (¬_)
open import Data.Nat using (suc)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.List.All using (All; []; _∷_)
open import Data.List.Any using (Any; here; there)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_)

open import RoutingLib.Data.List using (insert)
open import RoutingLib.Data.List.AllPairs using (AllPairs)
open import RoutingLib.Data.List.Uniqueness.Setoid using (Unique; []; _∷_)

module RoutingLib.Data.List.Relation.Permutation.Properties {a} {A : Set a} where
  
open import RoutingLib.Data.List.Relation.Permutation {a} {A}

------------------------------------------------------------------------
-- _⇿_ forms an equivalence class
  
⇿-refl : Reflexive _⇿_
⇿-refl {x = []}    = []
⇿-refl {x = _ ∷ _} = here ∷ ⇿-refl

⇿-sym : Symmetric _⇿_
⇿-sym []                    = []
⇿-sym (x◂xs≡xys ∷ zys⇿y∷xs) = x◂xs≡xys ∷ʳ ⇿-sym zys⇿y∷xs

⇿-trans : Transitive _⇿_
⇿-trans [] [] = []
⇿-trans (p ∷ ps) qqs with extract-permutation p qqs
... | _ , q , qs = q ∷ ⇿-trans ps qs

⇿-isEquivalence : IsEquivalence _⇿_
⇿-isEquivalence = record
  { refl  = ⇿-refl
  ; sym   = ⇿-sym
  ; trans = ⇿-trans
  }
  
⇿-setoid : Setoid a a
⇿-setoid = record
  { isEquivalence = ⇿-isEquivalence
  }

------------------------------------------------------------------------
-- Any

module _ {p} {P : A → Set p} where

  Any-◂≡ : ∀ {x xs ys} → Any P (x ∷ xs) → x ◂ xs ≡ ys → Any P ys
  Any-◂≡ pxs                 here             = pxs
  Any-◂≡ (here px)           (there x◂xs≡xss) = there (Any-◂≡ (here px) x◂xs≡xss)
  Any-◂≡ (there (here py))   (there x◂xs≡xss) = here py
  Any-◂≡ (there (there pxs)) (there x◂xs≡xss) = there (Any-◂≡ (there pxs) x◂xs≡xss)

  Any-⇿ : ∀ {xs ys} → Any P xs → xs ⇿ ys → Any P ys
  Any-⇿ (here px)   (x◂zs≡ys ∷ xs⇿zs) = Any-◂≡ (here px) x◂zs≡ys
  Any-⇿ (there pxs) (x◂zs≡ys ∷ xs⇿zs) = Any-◂≡ (there (Any-⇿ pxs xs⇿zs)) x◂zs≡ys

------------------------------------------------------------------------
-- All

module _ {p} {P : A → Set p} where

  ◂≡-pres-All : ∀ {x xs ys} → All P (x ∷ xs) → x ◂ xs ≡ ys → All P ys
  ◂≡-pres-All pxs               here            = pxs
  ◂≡-pres-All (px ∷ (py ∷ pxs)) (there x◂xs≡ys) =
    py ∷ ◂≡-pres-All (px ∷ pxs) x◂xs≡ys

  ⇿-pres-All : ∀ {xs ys} → All P xs → xs ⇿ ys → All P ys
  ⇿-pres-All []         []                = []
  ⇿-pres-All (px ∷ pxs) (x◂zs≡ys ∷ xs⇿zs) =
    ◂≡-pres-All (px ∷ (⇿-pres-All pxs xs⇿zs)) x◂zs≡ys

------------------------------------------------------------------------
-- AllPairs

module _ {ℓ} {_~_ : Rel A ℓ} (sym : Symmetric _~_) where

  ◂≡-pres-AllPairs : ∀ {x xs ys} → AllPairs _~_ (x ∷ xs) → x ◂ xs ≡ ys → AllPairs _~_ ys
  ◂≡-pres-AllPairs pxs                           here             = pxs
  ◂≡-pres-AllPairs ((x~z ∷ x~xs) ∷ (y~xs ∷ pxs)) (there x◂xs≡ys) =
    ◂≡-pres-All (sym x~z ∷ y~xs) x◂xs≡ys ∷ (◂≡-pres-AllPairs (x~xs ∷ pxs) x◂xs≡ys)

  ⇿-pres-AllPairs : ∀ {xs ys} → AllPairs _~_ xs → xs ⇿ ys → AllPairs _~_ ys
  ⇿-pres-AllPairs []           []                 = []
  ⇿-pres-AllPairs (x~xs ∷ pxs) (x◂zs≡ys ∷ xs⇿zs) =
    ◂≡-pres-AllPairs (⇿-pres-All x~xs xs⇿zs ∷ ⇿-pres-AllPairs pxs xs⇿zs) x◂zs≡ys

------------------------------------------------------------------------
-- insert

module _ {ℓ} {_≤_ : Rel A ℓ} (total : Total _≤_) where

  ⇿-insert⁺ : ∀ v {xs ys} → xs ⇿ ys → insert total v xs ⇿ v ∷ ys
  ⇿-insert⁺ v {[]}     []⇿ys             = here ∷ []⇿ys
  ⇿-insert⁺ v {x ∷ xs} (x◂xs≡ys ∷ xs⇿ys) with total v x
  ... | inj₁ _ = here ∷ (x◂xs≡ys ∷ xs⇿ys)
  ... | inj₂ _ = there x◂xs≡ys ∷ ⇿-insert⁺ v xs⇿ys
  
------------------------------------------------------------------------
-- _++_

◂≡-++ˡ : ∀ {x xs ys xxs} → x ◂ xs ≡ xxs → x ◂ (xs ++ ys) ≡ (xxs ++ ys)
◂≡-++ˡ here      = here
◂≡-++ˡ (there p) = there (◂≡-++ˡ p)

◂≡-++ʳ : ∀ {y xs ys yys} → y ◂ ys ≡ yys → y ◂ (xs ++ ys) ≡ (xs ++ yys)
◂≡-++ʳ {xs = []}     p = p
◂≡-++ʳ {xs = _ ∷ xs} p = there (◂≡-++ʳ {xs = xs} p)

⇿-++⁺ : ∀ {ws xs ys zs} → ws ⇿ ys → xs ⇿ zs → ws ++ xs ⇿ ys ++ zs
⇿-++⁺ [] xs⇿zs = xs⇿zs
⇿-++⁺ (x◂xs≡ys ∷ ws⇿ys) xs⇿zs = (◂≡-++ˡ x◂xs≡ys) ∷ (⇿-++⁺ ws⇿ys xs⇿zs)

------------------------------------------------------------------------
-- length

◂≡-length : ∀ {x xs xxs} → x ◂ xs ≡ xxs → length xxs ≡ suc (length xs)
◂≡-length here      = refl
◂≡-length (there p) = cong suc (◂≡-length p)

⇿-length : ∀ {xs ys} → xs ⇿ ys → length xs ≡ length ys
⇿-length []                 = refl
⇿-length (x◂xs≡xss ∷ xs⇿ys) = trans (cong suc (⇿-length xs⇿ys)) (sym (◂≡-length x◂xs≡xss))
