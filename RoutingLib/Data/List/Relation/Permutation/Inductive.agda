module RoutingLib.Data.List.Relation.Permutation.Inductive where

open import Data.List
open import Data.List.All
open import Data.List.Any
import Data.List.Membership.Setoid as Membership
open import Data.List.Relation.Permutation.Inductive
open import Data.List.Relation.Permutation.Inductive.Properties
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (∃₂; _,_)
open import Function using (_∘_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)
open import Relation.Unary using (Pred)

open import RoutingLib.Data.List using (insert)
open import RoutingLib.Data.List.AllPairs
open import RoutingLib.Data.List.Uniqueness.Setoid

open PermutationReasoning

module _ {a} {A : Set a} where

  split : ∀ (x : A) as bs {xs} → as ++ [ x ] ++ bs ↭ xs → ∃₂ λ ps qs → xs ≡ ps ++ [ x ] ++ qs
  split x []           bs {x ∷ bs}     refl          = []       , bs , refl
  split x (a ∷ [])     bs {a ∷ x ∷ bs} refl          = (a ∷ []) , bs , refl
  split x (a ∷ b ∷ as) bs {a ∷ b ∷ _}  refl          = a ∷ b ∷ as , bs , refl
  split x []           bs {a ∷ xs}     (prep a _)    = [] , xs , refl
  split x (a ∷ as)     bs {a ∷ xs}     (prep a ↭)   with split x as bs ↭
  ... | (ps , qs , refl) = a ∷ ps , qs , refl
  split x [] (b ∷ bs) {b ∷ x ∷ xs}     (swap x b _)  = [ b ] , xs , refl
  split x (a ∷ [])     bs {x ∷ a ∷ xs} (swap a x ↭)  = [] , a ∷ xs , refl
  split x (a ∷ b ∷ as) bs {b ∷ a ∷ xs} (swap a b ↭)  with split x as bs ↭
  ... | (ps , qs , refl) = b ∷ a ∷ ps , qs , refl
  split x as           bs {xs}         (trans ↭₁ ↭₂) with split x as bs ↭₁
  ... | (ps , qs , refl) = split x ps qs ↭₂

--------------------------------------------------------------------------------
-- Predicates

module _ {a p} {A : Set a} {P : Pred A p} where

  ↭-pres-Any : ∀ {xs ys} → xs ↭ ys → Any P xs → Any P ys
  ↭-pres-Any refl             pxs                 = pxs
  ↭-pres-Any (prep x xs↭ys)   (here px)           = here px
  ↭-pres-Any (prep x xs↭ys)   (there pxs)         = there (↭-pres-Any xs↭ys pxs)
  ↭-pres-Any (swap x y xs↭ys) (here px)           = there (here px)
  ↭-pres-Any (swap x y xs↭ys) (there (here py))   = here py
  ↭-pres-Any (swap x y xs↭ys) (there (there pxs)) = there (there (↭-pres-Any xs↭ys pxs))
  ↭-pres-Any (trans ↭₁ ↭₂)    pxs                 = ↭-pres-Any ↭₂ (↭-pres-Any ↭₁ pxs)
  
  ↭-pres-All : ∀ {xs ys} → xs ↭ ys → All P xs → All P ys
  ↭-pres-All refl                pxs             = pxs
  ↭-pres-All (prep x xs↭ys)      (px ∷ pxs)      = px ∷ ↭-pres-All xs↭ys pxs
  ↭-pres-All (swap x y xs↭ys)    (px ∷ py ∷ pxs) = py ∷ px ∷ ↭-pres-All xs↭ys pxs
  ↭-pres-All (trans xs↭zs ys↭zs) pxs             = ↭-pres-All ys↭zs (↭-pres-All xs↭zs pxs)

module _ {a ℓ} {A : Set a} {_∼_ : Rel A ℓ} (sym : Symmetric _∼_) where

  ↭-pres-AllPairs : ∀ {xs ys} → xs ↭ ys → AllPairs _∼_ xs → AllPairs _∼_ ys
  ↭-pres-AllPairs refl             pxs                         = pxs
  ↭-pres-AllPairs (prep x xs↭ys)   (x∼xs ∷ pxs)                = ↭-pres-All xs↭ys x∼xs ∷ ↭-pres-AllPairs xs↭ys pxs
  ↭-pres-AllPairs (swap x y xs↭ys) ((x∼y ∷ x~xs) ∷ y∼xs ∷ pxs) = (sym x∼y ∷ ↭-pres-All xs↭ys y∼xs) ∷ ↭-pres-All xs↭ys x~xs ∷ ↭-pres-AllPairs xs↭ys pxs
  ↭-pres-AllPairs (trans ↭₁ ↭₂)    pxs                         = ↭-pres-AllPairs ↭₂ (↭-pres-AllPairs ↭₁ pxs)

module _ {a ℓ} (S : Setoid a ℓ) where

  open Membership S
  
  ↭-pres-∈ : ∀ {x xs ys} → xs ↭ ys → x ∈ xs → x ∈ ys
  ↭-pres-∈ = ↭-pres-Any

module _ {a ℓ} (S : Setoid a ℓ) where

  open Setoid S
  
  ↭-pres-! : ∀ {xs ys} → xs ↭ ys → Unique S xs → Unique S ys
  ↭-pres-! xs↭ys xs! = ↭-pres-AllPairs (_∘ sym) xs↭ys xs!

--------------------------------------------------------------------------------
-- insert

module _ {a ℓ} {A : Set a} {_≤_ : Rel A ℓ} (total : Total _≤_) where

  insert⁺ : ∀ x {xs ys} → xs ↭ ys → insert total x xs ↭ x ∷ ys
  insert⁺ x {[]}     {ys} xs↭ys = prep x xs↭ys
  insert⁺ x {y ∷ xs} {ys} y∷xs↭ys with total x y
  ... | inj₁ _ = prep x y∷xs↭ys
  ... | inj₂ _ with split y [] xs y∷xs↭ys
  ...   | ps , qs , refl = begin
    y ∷ insert total x xs ↭⟨ prep y (insert⁺ x (drop-∷ (trans y∷xs↭ys (shift y ps qs)))) ⟩
    y ∷ x ∷ ps ++ qs      ↭⟨ swap y x refl ⟩
    x ∷ y ∷ ps ++ qs      ↭⟨ ↭-sym (prep x (shift y ps qs)) ⟩
    x ∷ ps ++ [ y ] ++ qs ∎
