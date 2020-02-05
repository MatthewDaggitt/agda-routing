open import Data.List hiding (head; tail)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_; here; there)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using (head; tail; Pointwise-length)
open import Data.List.Properties using (∷-injective; ∷-injectiveʳ; ∷-injectiveˡ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; s≤s; z≤n)
open import Data.Nat.Properties
open import Data.Nat.Induction
open import Data.Product using (∃₂; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_; flip)
open import Relation.Unary using (Decidable; Pred)
open import Relation.Binary hiding (Decidable)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open import RoutingLib.Data.List
open import RoutingLib.Data.Nat.Properties

import Data.List.Membership.Setoid as Membership
import Data.List.Membership.Setoid.Properties as Membershipₚ
import Data.List.Relation.Binary.Equality.Setoid as Equality
import Data.List.Relation.Binary.Permutation.Setoid as PermutationSetoid
import Data.List.Relation.Binary.Permutation.Setoid.Properties as PermutationSetoidProperties
import Data.List.Relation.Unary.Unique.Setoid as Unique
import RoutingLib.Data.List.Relation.Binary.Sublist.Setoid as Sublist

module RoutingLib.Data.List.Relation.Binary.Permutation.Setoid.Properties
  {a ℓ} (S : Setoid a ℓ)  where

open PermutationSetoidProperties S hiding (++⁺)
open PermutationSetoid S
open Sublist S
open Membership S hiding (_─_)
open Unique S hiding (head; tail)
open Equality S using (_≋_; []; _∷_; ≋-refl; ≋-sym; ≋-trans; ++⁺)
open module Eq = Setoid S using (_≈_; sym) renaming (Carrier to A)

xs↭ys⇒|xs|≡|ys| : ∀ {xs ys} → xs ↭ ys → length xs ≡ length ys
xs↭ys⇒|xs|≡|ys| (refl eq)            = Pointwise-length eq
xs↭ys⇒|xs|≡|ys| (prep eq xs↭ys)      = P.cong suc (xs↭ys⇒|xs|≡|ys| xs↭ys)
xs↭ys⇒|xs|≡|ys| (swap eq₁ eq₂ xs↭ys) = P.cong (λ x → suc (suc x)) (xs↭ys⇒|xs|≡|ys| xs↭ys)
xs↭ys⇒|xs|≡|ys| (trans xs↭ys xs↭ys₁) = P.trans (xs↭ys⇒|xs|≡|ys| xs↭ys) (xs↭ys⇒|xs|≡|ys| xs↭ys₁)

tabulate⁺ : ∀ {n} {f g : Fin n → A} →
            (∀ {i} → f i ≈ g i) → tabulate f ↭ tabulate g
tabulate⁺ {zero}  {f} {g} f=g = refl []
tabulate⁺ {suc k} {f} {g} f=g = prep f=g (tabulate⁺ {k} f=g)

module _ {ℓ} {_≤_ : Rel A ℓ} (total : Total _≤_) where

  insert⁺ : ∀ x {xs ys} → xs ↭ ys → insert total x xs ↭ x ∷ ys
  insert⁺ x {[]}     {ys} xs↭ys = prep Eq.refl xs↭ys
  insert⁺ x {y ∷ xs} {ys} y∷xs↭ys with total x y
  ... | inj₁ _ = prep Eq.refl y∷xs↭ys
  ... | inj₂ _ with split y [] xs (↭-sym y∷xs↭ys)
  ...   | ps , qs , eq = begin
    y ∷ insert total x xs ↭⟨ ↭-prep y (insert⁺ x {xs} {ps ++ qs}
                               (dropMiddleElement [] [] (trans (↭-respʳ-≋ eq y∷xs↭ys) (shift Eq.refl ps qs)))) ⟩
    y ∷ x ∷ ps ++ qs      ↭⟨ ↭-swap y x ↭-refl ⟩
    x ∷ y ∷ ps ++ qs      ↭⟨ ↭-sym (prep Eq.refl (shift Eq.refl ps qs)) ⟩
    x ∷ ps ++ [ y ] ++ qs ↭⟨ prep Eq.refl (≋⇒↭ (≋-sym eq)) ⟩
    x ∷ ys                ∎
    where open PermutationReasoning
