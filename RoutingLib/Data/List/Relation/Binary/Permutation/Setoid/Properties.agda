{-# OPTIONS --allow-unsolved-metas #-}

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
open import Data.Product using (_×_; ∃; ∃₂; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_; flip; Injective)
open import Level using (_⊔_)
open import Relation.Unary using (Pred) renaming (Decidable to Decidable₁)
open import Relation.Binary
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction; contraposition)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open import RoutingLib.Data.List
open import RoutingLib.Data.Nat.Properties

import Data.List.Membership.Setoid as Membership
import Data.List.Membership.DecSetoid as DecMembership
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
open module Eq = Setoid S using (_≈_)
  renaming (Carrier to A; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans; isEquivalence to ≈-isEquivalence)

xs↭ys⇒|xs|≡|ys| : ∀ {xs ys} → xs ↭ ys → length xs ≡ length ys
xs↭ys⇒|xs|≡|ys| (refl eq)            = Pointwise-length eq
xs↭ys⇒|xs|≡|ys| (prep eq xs↭ys)      = P.cong suc (xs↭ys⇒|xs|≡|ys| xs↭ys)
xs↭ys⇒|xs|≡|ys| (swap eq₁ eq₂ xs↭ys) = P.cong (λ x → suc (suc x)) (xs↭ys⇒|xs|≡|ys| xs↭ys)
xs↭ys⇒|xs|≡|ys| (trans xs↭ys xs↭ys₁) = P.trans (xs↭ys⇒|xs|≡|ys| xs↭ys) (xs↭ys⇒|xs|≡|ys| xs↭ys₁)

|xs|≠|ys|⇒¬xs↭ys : ∀ {xs} {ys} → ¬(length xs ≡ length ys) → ¬(xs ↭ ys)
|xs|≠|ys|⇒¬xs↭ys = contraposition xs↭ys⇒|xs|≡|ys|

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

↭-nil-cons : ∀ x xs → ¬([] ↭ x ∷ xs)
↭-nil-cons x xs = |xs|≠|ys|⇒¬xs↭ys λ ()

↭-cons-nil : ∀ x xs → ¬(x ∷ xs ↭ [])
↭-cons-nil x xs = |xs|≠|ys|⇒¬xs↭ys λ ()

↭⇒cons-∈ : ∀ {x xs ys} → x ∷ xs ↭ ys → x ∈ ys
↭⇒cons-∈ (refl (x≈y ∷ _))      = here x≈y
↭⇒cons-∈ (prep x≈y _)          = here x≈y
↭⇒cons-∈ (swap x₁≈y₂ _ _)      = there (here x₁≈y₂)
↭⇒cons-∈ (trans x∷xs↭zs zs↭ys) = ∈-resp-↭ zs↭ys (↭⇒cons-∈ x∷xs↭zs)

∃₃ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : ∀ {x} → A → B x → Set c}
     (D : (x : A) → (y : B x) → C x y → Set d) → Set (a ⊔ b ⊔ c ⊔ d)
∃₃ D = ∃ λ a → ∃ λ b → ∃ λ c → D a b c

split-∈ : ∀ {x zs} → x ∈ zs → ∃₃ (λ ys y ws → (x ≈ y) × (zs ≋ ys ++ [ y ] ++ ws))
split-∈ {x} {z ∷ zs} (here x≈z)   = [] , z , zs , x≈z , ≋-refl
split-∈ {x} {z ∷ zs} (there x∈zs) =
  let (ys , y , ws , x=y , zs=ys++y++ws) = split-∈ x∈zs in
  z ∷ ys , y , ws , x=y , ≈-refl ∷ zs=ys++y++ws

module _ (_≟_ : Decidable _≈_) where

  ≈-isDecEquivalence : IsDecEquivalence _≈_
  ≈-isDecEquivalence = record
    { isEquivalence = ≈-isEquivalence
    ; _≟_           = _≟_
    }

  DS : DecSetoid a ℓ
  DS = record
    { Carrier          = A
    ; _≈_              = _≈_
    ; isDecEquivalence = ≈-isDecEquivalence
    }

  open DecMembership DS using (_∈?_)
  open PermutationReasoning

  infix 3 _↭?_

  _↭?_ : Decidable _↭_
  [] ↭? []       = yes (refl [])
  [] ↭? (y ∷ ys) = no (↭-nil-cons y ys)
  (x ∷ xs) ↭? ys with x ∈? ys
  ... | no x∉ys  = no ((contraposition ↭⇒cons-∈) x∉ys)
  ... | yes x∈ys = prf (split-∈ x∈ys)
    where
    prf : ∃₃ (λ zs y ws → (x ≈ y) × (ys ≋ zs ++ [ y ] ++ ws)) → Dec ((x ∷ xs) ↭ ys)
    prf (zs , y , ws , x=y , ys=zs++y++ws) with xs ↭? zs ++ ws
    ... | yes xs↭zs++ws = yes (begin
              x ∷ xs            <⟨ xs↭zs++ws ⟩
              x ∷ (zs ++ ws)    ↭⟨ ↭-sym (shift (≈-sym x=y) zs ws) ⟩
              zs ++ [ y ] ++ ws ↭⟨ ↭-sym (≋⇒↭ ys=zs++y++ws) ⟩
              ys                ∎)
    ... | no xs¬↭zs++ws = no λ x∷xs↭ys → contradiction (dropMiddleElement [] [] (x∷xs↭x∷zs++ws x∷xs↭ys)) xs¬↭zs++ws
      where
      x∷xs↭x∷zs++ws : x ∷ xs ↭ ys → x ∷ xs ↭ x ∷ zs ++ ws
      x∷xs↭x∷zs++ws x∷xs↭ys = begin
        x ∷ xs            ↭⟨ x∷xs↭ys ⟩
        ys                ↭⟨ ≋⇒↭ ys=zs++y++ws ⟩
        zs ++ [ y ] ++ ws ↭⟨ shift (≈-sym x=y) zs ws ⟩
        x ∷ zs ++ ws ∎
