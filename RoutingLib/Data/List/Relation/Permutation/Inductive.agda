module RoutingLib.Data.List.Relation.Permutation.Inductive where

open import Data.List
open import Data.List.Relation.Permutation.Inductive
open import Data.List.Relation.Permutation.Inductive.Properties
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (∃₂; _,_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

open import RoutingLib.Data.List using (insert)

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
