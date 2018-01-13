open import Relation.Binary using (Setoid; Rel; Reflexive; Symmetric; Transitive; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (¬_)
open import Data.Nat using (suc)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.List.All using (All; []; _∷_)
open import Data.List.Any using (Any; here; there)
open import Data.Product using (_,_)
open import Function using (_∘_)

open import RoutingLib.Data.List.All using (AllPairs)
open import RoutingLib.Data.List.Uniqueness.Setoid using (Unique; []; _∷_)


module RoutingLib.Data.List.Permutation.Properties {a} {A : Set a} where
  
  open import RoutingLib.Data.List.Permutation {a} {A}

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
    { Carrier       = List A
    ; _≈_           = _⇿_
    ; isEquivalence = ⇿-isEquivalence
    }


  -- Other properties

  ◂≡-length : ∀ {x xs xxs} → x ◂ xs ≡ xxs → length xxs ≡ suc (length xs)
  ◂≡-length here      = refl
  ◂≡-length (there p) = cong suc (◂≡-length p)
  
  ⇿-length : ∀ {xs ys} → xs ⇿ ys → length xs ≡ length ys
  ⇿-length []                 = refl
  ⇿-length (x◂xs≡xss ∷ xs⇿ys) = trans (cong suc (⇿-length xs⇿ys)) (sym (◂≡-length x◂xs≡xss))


  

  ◂≡-++ˡ : ∀ {x xs ys xxs} → x ◂ xs ≡ xxs → x ◂ (xs ++ ys) ≡ (xxs ++ ys)
  ◂≡-++ˡ here      = here
  ◂≡-++ˡ (there p) = there (◂≡-++ˡ p)
  
  ◂≡-++ʳ : ∀ {y xs ys yys} → y ◂ ys ≡ yys → y ◂ (xs ++ ys) ≡ (xs ++ yys)
  ◂≡-++ʳ {xs = []}     p = p
  ◂≡-++ʳ {xs = _ ∷ xs} p = there (◂≡-++ʳ {xs = xs} p)

  ⇿-++ : ∀ {ws xs ys zs} → ws ⇿ ys → xs ⇿ zs → ws ++ xs ⇿ ys ++ zs
  ⇿-++ [] xs⇿zs = xs⇿zs
  ⇿-++ (x◂xs≡ys ∷ ws⇿ys) xs⇿zs = (◂≡-++ˡ x◂xs≡ys) ∷ (⇿-++ ws⇿ys xs⇿zs)
