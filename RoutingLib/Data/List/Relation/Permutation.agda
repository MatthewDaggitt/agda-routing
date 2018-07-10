open import Relation.Binary using (Rel; Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (∃; ∃₂; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Nat using (suc)

open import RoutingLib.Data.List.Uniqueness.Setoid using (Unique)

module RoutingLib.Data.List.Relation.Permutation {a} {A : Set a} where

  infix 5 _∷_
  infix 4 _⇿_

  -- "x ◂ xs ≡ xys" means that xys is equal to "xs with x inserted somewhere in it"
  data _◂_≡_ (x : A) : List A → List A → Set a where
    here  : ∀ {xs}       → x ◂ xs ≡ (x ∷ xs)
    there : ∀ {y xs xxs} → x ◂ xs ≡ xxs → x ◂ (y ∷ xs) ≡ (y ∷ xxs)

  data _⇿_ : Rel (List A) a where
    []  : [] ⇿ []
    _∷_ : ∀ {x xs ys xxs} → x ◂ xs ≡ xxs → ys ⇿ xs → (x ∷ ys) ⇿ xxs

  _∷ʳ_ : ∀ {x xs ys xys} → x ◂ ys ≡ xys → ys ⇿ xs → xys ⇿ (x ∷ xs)
  _∷ʳ_ here      p        = here ∷ p
  _∷ʳ_ (there y) (p ∷ ps) = there p ∷ (y ∷ʳ ps)

  ◂≡-bridge : ∀ {x y xs xxs yxxs} → x ◂ xs ≡ xxs → y ◂ xxs ≡ yxxs → ∃ λ yxs → (y ◂ xs ≡ yxs) × (x ◂ yxs ≡ yxxs)
  ◂≡-bridge p         here      = _ , here , there p
  ◂≡-bridge here      (there q) = _ , q    , here
  ◂≡-bridge (there p) (there q) with ◂≡-bridge p q
  ... | _ , p' , q' = _ , there p' , there q'

  extract-permutation : ∀ {x ys zs zs'} → x ◂ ys ≡ zs → zs ⇿ zs' → ∃ λ ys' → (x ◂ ys' ≡ zs') × ys ⇿ ys'
  extract-permutation here (q ∷ qs) = _ , q , qs
  extract-permutation (there p) (q ∷ qs) with extract-permutation p qs
  ... | ys' , r , rs with ◂≡-bridge r q
  ...   | ys'' , s , t = ys'' , t , s ∷ rs

