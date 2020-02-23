{-# OPTIONS --allow-unsolved-metas #-}

open import Data.List hiding (head; tail)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_; here; there)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using (head; tail)
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
open module Eq = Setoid S using (_≈_) renaming (Carrier to A; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans; isEquivalence to ≈-isEquivalence)

len : ∀ {xs ys} → xs ↭ ys → ℕ
len refl                 = 1
len (prep eq xs↭ys)      = suc (len xs↭ys)
len (swap eq₁ eq₂ xs↭ys) = suc (len xs↭ys)
len (trans xs↭ys xs↭ys₁) = len xs↭ys + len xs↭ys₁

0<len : ∀ {xs ys} (xs↭ys : xs ↭ ys) → 0 < len xs↭ys
0<len refl                 = s≤s z≤n
0<len (prep eq xs↭ys)      = ≤-step (0<len xs↭ys)
0<len (swap eq₁ eq₂ xs↭ys) = ≤-step (0<len xs↭ys)
0<len (trans xs↭ys xs↭ys₁) = <-transˡ (0<len xs↭ys) (m≤m+n (len xs↭ys) (len xs↭ys₁))

split : ∀ (v : A) as bs {xs} → (p : as ++ [ v ] ++ bs ↭ xs) → Acc _<_ (len p) → ∃₂ λ ps qs → xs ≋ ps ++ [ v ] ++ qs
split v []           bs {x ∷ bs}     refl         _ = []       , bs , ≋-refl
split v (a ∷ [])     bs {x ∷ y ∷ bs} refl         _ = (a ∷ []) , bs , ≋-refl
split v (a ∷ b ∷ as) bs {a ∷ b ∷ _}  refl         _ = a ∷ b ∷ as , bs , ≋-refl
split v []           bs {x ∷ xs}     (prep v≈x _) _ = [] , xs , ≈-sym v≈x ∷ ≋-refl
split v (a ∷ as)     bs {x ∷ xs}     (prep eq as↭xs)  (acc rec) with split v as bs as↭xs (rec _ ≤-refl)
... | (ps , qs , eq₂) = a ∷ ps , qs , Eq.sym eq ∷ eq₂
split v [] (b ∷ bs) {x ∷ y ∷ xs}     (swap y≈v b≈x _) _ = [ b ] , xs , ≈-sym b≈x ∷ ≈-sym y≈v ∷ ≋-refl
split v (a ∷ [])     bs {x ∷ y ∷ xs} (swap a≈y v≈x ↭) _ = [] , a ∷ xs , ≈-sym v≈x ∷ ≈-sym a≈y ∷ ≋-refl
split v (a ∷ b ∷ as) bs {x ∷ y ∷ xs} (swap a≈y b≈x as↭xs) (acc rec) with split v as bs as↭xs (rec _ ≤-refl)
... | (ps , qs , eq) = b ∷ a ∷ ps , qs , ≈-sym b≈x ∷ ≈-sym a≈y ∷ eq
split v as           bs {xs}         (trans ↭₁ ↭₂) (acc rec) with split v as bs ↭₁ (rec _ (m<m+n (len ↭₁) (0<len ↭₂)))
... | (ps , qs , eq) = split v ps qs (↭-respˡ-≋ eq ↭₂) (rec _ (begin-strict
  len (↭-respˡ-≋ eq ↭₂) ≡⟨ lemma eq ↭₂ ⟩
  len ↭₂                <⟨ m<n+m (len ↭₂) (0<len ↭₁) ⟩
  len ↭₁ + len ↭₂       ∎))
  where
  open ≤-Reasoning

  -- Will be true once Agda stdlib issue #1002 is fixed
  postulate lem′ : ∀ {xs ys} (xs≋ys : xs ≋ ys) → len (≋⇒↭ xs≋ys) ≡ 1
  
  lemma : ∀ {xs ys zs} (ys≋xs : ys ≋ xs) (ys↭zs : ys ↭ zs) → len (↭-respˡ-≋ ys≋xs ys↭zs) ≡ len ys↭zs
  lemma xs≋ys               refl                 = lem′ (≋-sym xs≋ys)
  lemma (y≈x ∷ ys≋xs)       (prep eq ys↭zs)      = P.cong suc (lemma ys≋xs ys↭zs)
  lemma (y≈x ∷ z≈w ∷ ys≋xs) (swap eq₁ eq₂ ys↭zs) = P.cong suc (lemma ys≋xs ys↭zs)
  lemma ys≋xs               (trans ys↭zs ys↭zs₁) = P.cong (_+ len ys↭zs₁) (lemma ys≋xs ys↭zs)


drop-mid-≋ : ∀ {x} ws xs {ys} {zs} →
           ws ++ [ x ] ++ ys ≋ xs ++ [ x ] ++ zs →
           ws ++ ys ↭ xs ++ zs
drop-mid-≋ []       []       (_   ∷ eq) = ≋⇒↭ eq
drop-mid-≋ []       (x ∷ xs) (w≈v ∷ eq) = ↭-respˡ-≋ (≋-sym eq) (shift w≈v xs _)
drop-mid-≋ (w ∷ ws) []       (w≈x ∷ eq) = ↭-respʳ-≋ eq (↭-sym (shift (Eq.sym w≈x) ws _))
drop-mid-≋ (w ∷ ws) (x ∷ xs) (w≈x ∷ eq) = prep w≈x (drop-mid-≋ ws xs eq)

drop-mid : ∀ {v} ws xs {ys zs} →
         ws ++ [ v ] ++ ys ↭ xs ++ [ v ] ++ zs →
         ws ++ ys ↭ xs ++ zs
drop-mid {v} ws xs p = drop-mid′ p ws xs ≋-refl ≋-refl
  where
  open PermutationReasoning
  drop-mid′ : ∀ {l′ l″ : List A} → l′ ↭ l″ →
              ∀ ws xs {ys zs : List A} →
              ws ++ [ v ] ++ ys ≋ l′ →
              xs ++ [ v ] ++ zs ≋ l″ →
              ws ++ ys ↭ xs ++ zs
  drop-mid′ {_}      {_} refl             ws           xs           {ys} {zs} eq1 eq2 = drop-mid-≋ ws xs (≋-trans eq1 (≋-sym eq2))
  drop-mid′ {_ ∷ as} {_ ∷ bs} (prep _ p)       []           []           {ys} {zs} eq1 eq2 = begin
    ys           ↭⟨ ≋⇒↭ (tail eq1) ⟩
    as           ↭⟨ p ⟩
    bs           ↭⟨ ≋⇒↭ (≋-sym (tail eq2)) ⟩
    zs           ∎
  drop-mid′ {_ ∷ as} {_ ∷ bs} (prep v≈x p)     []           (x ∷ xs)     {ys} {zs} eq1 eq2 = begin
    ys           ↭⟨ ≋⇒↭ (tail eq1) ⟩
    as           ↭⟨ p ⟩
    bs           ↭⟨ ≋⇒↭ (≋-sym (tail eq2)) ⟩
    xs ++ v ∷ zs ↭⟨ shift (Eq.trans (Eq.trans (head eq1) v≈x) (Eq.sym (head eq2))) xs zs ⟩
    x ∷ xs ++ zs ∎
  drop-mid′ {_ ∷ as} {_ ∷ bs} (prep v≈w p)     (w ∷ ws)     []           {ys} {zs} eq1 eq2 = begin
    w ∷ ws ++ ys ↭⟨ ↭-sym (shift (Eq.trans (Eq.trans (head eq2) (Eq.sym v≈w)) (Eq.sym (head eq1))) ws ys) ⟩
    ws ++ v ∷ ys ↭⟨ ≋⇒↭ (tail eq1) ⟩
    as           ↭⟨ p ⟩
    bs           ↭⟨ ≋⇒↭ (≋-sym (tail eq2)) ⟩
    zs           ∎
  drop-mid′ {_ ∷ as} {_ ∷ bs} (prep w≈x p)     (w ∷ ws)     (x ∷ xs)     {ys} {zs} eq1 eq2 = begin
    w ∷ ws ++ ys ↭⟨ prep (Eq.trans (Eq.trans (head eq1) w≈x) (Eq.sym (head eq2))) (drop-mid′ p ws xs (tail eq1) (tail eq2)) ⟩
    x ∷ xs ++ zs ∎
  drop-mid′ {_ ∷ a ∷ as} {_ ∷ b ∷ bs} (swap v≈x y≈v p) []           []           {ys} {zs} eq1 eq2 = begin
    ys           ↭⟨ ≋⇒↭ (tail eq1) ⟩
    a ∷ as       ↭⟨ prep (Eq.trans (Eq.trans (Eq.trans y≈v (Eq.sym (head eq2))) (head eq1)) v≈x) p ⟩
    b ∷ bs       ↭⟨ ≋⇒↭ (≋-sym (tail eq2)) ⟩
    zs           ∎
  drop-mid′ {_ ∷ a ∷ as} {_ ∷ b ∷ bs} (swap v≈w y≈w p) []           (x ∷ [])     {ys} {zs} eq1 eq2 = begin
    ys           ↭⟨ ≋⇒↭ (tail eq1) ⟩
    a ∷ as       ↭⟨ prep y≈w p ⟩
    _ ∷ bs       ↭⟨ ≋⇒↭ (≋-sym (head eq2 ∷ tail (tail eq2))) ⟩
    x ∷ zs       ∎
  drop-mid′ {_ ∷ a ∷ as} {_ ∷ b ∷ bs} (swap v≈w y≈x p) []           (x ∷ w ∷ xs) {ys} {zs} eq1 eq2 = begin
    ys               ↭⟨ ≋⇒↭ (tail eq1) ⟩
    a ∷ as           ↭⟨ prep y≈x p ⟩
    _ ∷ bs           ↭⟨ ≋⇒↭ (≋-sym (head eq2 ∷ tail (tail eq2))) ⟩
    x ∷ xs ++ v ∷ zs ↭⟨ prep Eq.refl (shift (Eq.trans (head eq1) (Eq.trans v≈w (Eq.sym (head (tail eq2))))) xs zs) ⟩
    x ∷ w ∷ xs ++ zs ∎
  drop-mid′ {_ ∷ a ∷ as} {_ ∷ b ∷ bs} (swap w≈x _ p)   (w ∷ [])     []           {ys} {zs} eq1 eq2 = begin
    w ∷ ys ↭⟨ ≋⇒↭ (head eq1 ∷ tail (tail eq1)) ⟩
    _ ∷ as ↭⟨ prep w≈x p ⟩
    b ∷ bs ↭⟨ ≋⇒↭ (≋-sym (tail eq2)) ⟩
    zs     ∎
  drop-mid′ {_ ∷ a ∷ as} {_ ∷ b ∷ bs} (swap w≈y x≈v p) (w ∷ x ∷ ws) []           {ys} {zs} eq1 eq2 = begin
    w ∷ x ∷ ws ++ ys ↭⟨ prep Eq.refl (↭-sym (shift (Eq.trans (head eq2) (Eq.trans (Eq.sym x≈v) (Eq.sym (head (tail eq1))))) ws ys)) ⟩
    w ∷ ws ++ v ∷ ys ↭⟨ ≋⇒↭ (head eq1 ∷ tail (tail eq1)) ⟩
    _ ∷ as           ↭⟨ prep w≈y p ⟩
    b ∷ bs           ↭⟨ ≋⇒↭ (≋-sym (tail eq2)) ⟩
    zs               ∎
  drop-mid′ {_ ∷ a ∷ as} {_ ∷ b ∷ bs} (swap x≈v v≈y p) (x ∷ [])     (y ∷ [])     {ys} {zs} eq1 eq2 = begin
    x ∷ ys ↭⟨ ≋⇒↭ (head eq1 ∷ tail (tail eq1)) ⟩
    _ ∷ as ↭⟨ prep (Eq.trans x≈v (Eq.trans (Eq.sym (head (tail eq2))) (Eq.trans (head (tail eq1)) v≈y))) p ⟩
    _ ∷ bs ↭⟨ ≋⇒↭ (≋-sym (head eq2 ∷ tail (tail eq2))) ⟩
    y ∷ zs ∎
  drop-mid′ {_ ∷ a ∷ as} {_ ∷ b ∷ bs} (swap y≈w v≈z p) (y ∷ [])     (z ∷ w ∷ xs) {ys} {zs} eq1 eq2 = begin
    y ∷ ys           ↭⟨ ≋⇒↭ (head eq1 ∷ tail (tail eq1)) ⟩
    _ ∷ as           ↭⟨ prep y≈w p ⟩
    _ ∷ bs           ↭⟨ ≋⇒↭ (≋-sym (tail eq2)) ⟩
    w ∷ xs ++ v ∷ zs ↭⟨ prep Eq.refl (shift Eq.refl xs zs) ⟩
    w ∷ v ∷ xs ++ zs ↭⟨ swap Eq.refl (Eq.trans (head (tail eq1)) (Eq.trans v≈z (Eq.sym (head eq2)))) refl ⟩
    z ∷ w ∷ xs ++ zs ∎
  drop-mid′ {_ ∷ a ∷ as} {_ ∷ b ∷ bs} (swap y≈v w≈z p) (y ∷ w ∷ ws) (z ∷ []) {ys} {zs}    eq1 eq2 = begin
    y ∷ w ∷ ws ++ ys ↭⟨ swap (Eq.trans (head eq1) (Eq.trans y≈v (Eq.sym (head (tail eq2))))) Eq.refl refl ⟩
    w ∷ v ∷ ws ++ ys ↭⟨ prep Eq.refl (↭-sym (shift Eq.refl ws ys)) ⟩
    w ∷ ws ++ v ∷ ys ↭⟨ ≋⇒↭ (tail eq1) ⟩
    _ ∷ as           ↭⟨ prep w≈z p ⟩
    _ ∷ bs           ↭⟨ ≋⇒↭ (≋-sym (head eq2 ∷ tail (tail eq2))) ⟩
    z ∷ zs           ∎
  drop-mid′ (swap x≈z y≈w p) (x ∷ y ∷ ws) (w ∷ z ∷ xs) {ys} {zs} eq1 eq2 = begin
    x ∷ y ∷ ws ++ ys ↭⟨ swap
      (Eq.trans (head eq1) (Eq.trans x≈z (Eq.sym (head (tail eq2)))))
      (Eq.trans (head (tail eq1)) (Eq.trans y≈w (Eq.sym (head eq2))))
      (drop-mid′ p ws xs (tail (tail eq1)) (tail (tail eq2))) ⟩
    w ∷ z ∷ xs ++ zs ∎
  drop-mid′ {as} {bs} (trans p₁ p₂) ws xs eq1 eq2
    with Membershipₚ.∈-∃++ S (∈-resp-↭ (↭-respˡ-≋ (≋-sym eq1) p₁) (Membershipₚ.∈-insert S ws Eq.refl))
  ... | (h , t , w , v≈w , eq) = trans
    (drop-mid′ p₁ ws h eq1 (≋-trans (++⁺ ≋-refl (v≈w ∷ ≋-refl)) (≋-sym eq)))
    (drop-mid′ p₂ h xs (≋-trans (++⁺ ≋-refl (v≈w ∷ ≋-refl)) (≋-sym eq)) eq2)

drop-∷ : ∀ {x : A} {xs ys} → x ∷ xs ↭ x ∷ ys → xs ↭ ys
drop-∷ = drop-mid [] []

match : ∀ {xs ys} → xs ↭ ys → Fin (length xs) → Fin (length ys)
match refl                 i             = i
match (prep _ xs↭ys)      zero          = Fin.zero
match (prep _ xs↭ys)      (suc i)       = suc (match xs↭ys i)
match (swap _ _ xs↭ys)    zero          = suc zero
match (swap _ _ xs↭ys)    (suc zero)    = zero
match (swap _ _ xs↭ys)    (suc (suc i)) = suc (suc (match xs↭ys i)) 
match (trans xs↭zs zs↭ys) i             = match zs↭ys (match xs↭zs i)

match-lookup : ∀ {xs ys} (xs↭ys : xs ↭ ys) → ∀ i → lookup xs i ≈ lookup ys (match xs↭ys i)
match-lookup refl                 i             = Eq.refl
match-lookup (prep x≈y xs↭ys)     zero          = x≈y
match-lookup (prep _   xs↭ys)     (suc i)       = match-lookup xs↭ys i
match-lookup (swap x≈x' _ xs↭ys)  zero          = x≈x'
match-lookup (swap _ y≈y' xs↭ys)  (suc zero)    = y≈y'
match-lookup (swap eq₁ eq₂ xs↭ys) (suc (suc i)) = match-lookup xs↭ys i 
match-lookup (trans xs↭zs zs↭ys)  i             = Eq.trans (match-lookup xs↭zs i) (match-lookup zs↭ys (match xs↭zs i))

match-─ : ∀ {xs ys} (xs↭ys : xs ↭ ys) → ∀ i → (xs ─ i) ↭ (ys ─ match xs↭ys i)
match-─ refl                 i             = refl
match-─ (prep _ xs↭ys)       zero          = xs↭ys
match-─ (prep x≈y  xs↭ys)    (suc i)       = prep x≈y (match-─ xs↭ys i)
match-─ (swap _ y≈y' xs↭ys)  zero          = prep y≈y' xs↭ys
match-─ (swap x≈x' _ xs↭ys)  (suc zero)    = prep x≈x' xs↭ys
match-─ (swap eq₁ eq₂ xs↭ys) (suc (suc i)) = swap eq₁ eq₂ (match-─ xs↭ys i) 
match-─ (trans xs↭zs zs↭ys)  i             = trans (match-─ xs↭zs i) (match-─ zs↭ys (match xs↭zs i))


xs↭ys⇒|xs|≡|ys| : ∀ {xs ys} → xs ↭ ys → length xs ≡ length ys
xs↭ys⇒|xs|≡|ys| refl                 = P.refl
xs↭ys⇒|xs|≡|ys| (prep eq xs↭ys)      = P.cong suc (xs↭ys⇒|xs|≡|ys| xs↭ys)
xs↭ys⇒|xs|≡|ys| (swap eq₁ eq₂ xs↭ys) = P.cong (λ x → suc (suc x)) (xs↭ys⇒|xs|≡|ys| xs↭ys)
xs↭ys⇒|xs|≡|ys| (trans xs↭ys xs↭ys₁) = P.trans (xs↭ys⇒|xs|≡|ys| xs↭ys) (xs↭ys⇒|xs|≡|ys| xs↭ys₁)

|xs|≠|ys|⇒¬xs↭ys : ∀ {xs} {ys} → ¬(length xs ≡ length ys) → ¬(xs ↭ ys)
|xs|≠|ys|⇒¬xs↭ys = contraposition xs↭ys⇒|xs|≡|ys|

module _ {p} {P : Pred A p} (P? : Decidable₁ P) (P≈ : P Respects _≈_) where

  filter⁺ : ∀ {xs ys : List A} → xs ↭ ys → filter P? xs ↭ filter P? ys
  filter⁺ refl = refl
  filter⁺ (trans xs↭zs zs↭ys) = trans (filter⁺ xs↭zs) (filter⁺ zs↭ys)
  filter⁺ {x ∷ xs} {y ∷ ys} (prep x=x' A=A') with P? x | P? y
  ... | yes Px | yes Px' = prep x=x' (filter⁺ A=A')
  ... | yes Px | no ¬Px' = contradiction (P≈ x=x' Px) ¬Px'
  ... | no ¬Px | yes Px' = contradiction (P≈ (≈-sym x=x') Px') ¬Px
  ... | no ¬Px | no ¬Px' = filter⁺ A=A'
  filter⁺ {x ∷ y ∷ A} {y' ∷ x' ∷ A'} (swap x=x' y=y' A=A') with P? x | P? y'
  ... | no ¬Px | no ¬Py' = prf
    where
    prf : filter P? (y ∷ A) ↭ filter P? (x' ∷ A')
    prf with P? x' | P? y
    ... | no ¬Px' | no ¬Py = filter⁺ A=A'
    ... | no ¬Px' | yes Py = contradiction (P≈ y=y' Py) ¬Py'
    ... | yes Px' | _      = contradiction (P≈ (≈-sym x=x') Px') ¬Px
  ... | no ¬Px | yes Py' = prf
    where
    prf : filter P? (y ∷ A) ↭ y' ∷ filter P? (x' ∷ A')
    prf with
          P? x'   | P? y
    ... | no ¬Px' | no ¬Py = contradiction (P≈ (≈-sym y=y') Py') ¬Py
    ... | no ¬Px' | yes Py = prep y=y' (filter⁺ A=A')
    ... | yes Px' | _      = contradiction (P≈ (≈-sym x=x') Px') ¬Px
  ... | yes Px | no ¬Py' = prf
    where
    prf : x ∷ filter P? (y ∷ A) ↭ filter P? (x' ∷ A')
    prf with P? x' | P? y
    ... | no ¬Px' | _      = contradiction (P≈ x=x' Px) ¬Px'
    ... | yes Px' | no ¬Py = prep x=x' (filter⁺ A=A')
    ... | yes Px' | yes Py = contradiction (P≈ y=y' Py) ¬Py'
  ... | yes Px | yes Py' = prf
    where
    prf : x ∷ filter P? (y ∷ A) ↭ y' ∷ filter P? (x' ∷ A')
    prf with P? x' | P? y
    ... | no ¬Px' | _      = contradiction (P≈ x=x' Px) ¬Px'
    ... | yes Px' | no ¬Py = contradiction (P≈ (≈-sym y=y') Py') ¬Py
    ... | yes Px' | yes Py = swap x=x' y=y' (filter⁺ A=A')

tabulate⁺ : ∀ {n} {f g : Fin n → A} →
            (∀ {i} → f i ≈ g i) → tabulate f ↭ tabulate g
tabulate⁺ {zero}  {f} {g} f=g = refl
tabulate⁺ {suc k} {f} {g} f=g = prep f=g (tabulate⁺ {k} f=g)

module _ {ℓ} {_≤_ : Rel A ℓ} (total : Total _≤_) where

  insert⁺ : ∀ x {xs ys} → xs ↭ ys → insert total x xs ↭ x ∷ ys
  insert⁺ x {[]}     {ys} xs↭ys = prep Eq.refl xs↭ys
  insert⁺ x {y ∷ xs} {ys} y∷xs↭ys with total x y
  ... | inj₁ _ = prep Eq.refl y∷xs↭ys
  ... | inj₂ _ with split y [] xs y∷xs↭ys (<-wellFounded _)
  ...   | ps , qs , eq = begin
    y ∷ insert total x xs ↭⟨ prep Eq.refl (insert⁺ x {xs} {ps ++ qs} (drop-∷ {y} (trans (↭-respʳ-≋ eq y∷xs↭ys) (shift Eq.refl ps qs)))) ⟩
    y ∷ x ∷ ps ++ qs      ↭⟨ swap Eq.refl Eq.refl refl ⟩
    x ∷ y ∷ ps ++ qs      ↭⟨ ↭-sym (prep Eq.refl (shift Eq.refl ps qs)) ⟩
    x ∷ ps ++ [ y ] ++ qs ↭⟨ prep Eq.refl (≋⇒↭ (≋-sym eq)) ⟩
    x ∷ ys                ∎
    where open PermutationReasoning

↭-nil-cons : ∀ x xs → ¬([] ↭ x ∷ xs)
↭-nil-cons x xs = |xs|≠|ys|⇒¬xs↭ys λ ()

↭-cons-nil : ∀ x xs → ¬(x ∷ xs ↭ [])
↭-cons-nil x xs = |xs|≠|ys|⇒¬xs↭ys λ ()

↭⇒cons-∈ : ∀ {x xs ys} → x ∷ xs ↭ ys → x ∈ ys
↭⇒cons-∈ refl = here ≈-refl
↭⇒cons-∈ (prep x≈y x∷xs↭y∷ys) = here x≈y
↭⇒cons-∈ (swap x₁≈y₂ x₂≈y₁ x₁∷x₂∷xs↭y₁∷y₂∷ys) = there (here x₁≈y₂)
↭⇒cons-∈ (trans x∷xs↭zs zs↭ys) = ∈-resp-↭ zs↭ys (↭⇒cons-∈ x∷xs↭zs)

∃₃ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : ∀ {x} → A → B x → Set c}
     (D : (x : A) → (y : B x) → C x y → Set d) → Set (a ⊔ b ⊔ c ⊔ d)
∃₃ D = ∃ λ a → ∃ λ b → ∃ λ c → D a b c

split-∈ : ∀ {x zs} → x ∈ zs → ∃₃ (λ ys y ws → (x ≈ y) × (zs ≋ ys ++ [ y ] ++ ws))
split-∈ {x} {z ∷ zs} (here x≈z)   = [] , z , zs , x≈z , ≋-refl
split-∈ {x} {z ∷ zs} (there x∈zs) =
  let (ys , y , ws , x=y , zs=ys++y++ws) = split-∈ x∈zs in
  z ∷ ys , y , ws , x=y , ≈-refl ∷ zs=ys++y++ws

∷-injective-↭ : ∀ {z z' xs ys} → z ≈ z' → z ∷ xs ↭ z' ∷ ys → xs ↭ ys
∷-injective-↭ z=z' refl = refl
∷-injective-↭ z=z' (prep _ xs↭ys) = xs↭ys
∷-injective-↭ z=z' (swap z=y x=z' xs↭ys) = prep (≈-trans x=z' (≈-trans (≈-sym z=z') z=y)) xs↭ys
∷-injective-↭ z=z' (trans z∷xs↭ws ws↭z'∷ys) = {!!}

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
  [] ↭? []       = yes refl
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
    ... | no xs¬↭zs++ws = no λ x∷xs↭ys → contradiction (∷-injective-↭ ≈-refl (x∷xs↭x∷zs++ws x∷xs↭ys)) xs¬↭zs++ws
      where
      x∷xs↭x∷zs++ws : x ∷ xs ↭ ys → x ∷ xs ↭ x ∷ zs ++ ws
      x∷xs↭x∷zs++ws x∷xs↭ys = begin
        x ∷ xs            ↭⟨ x∷xs↭ys ⟩
        ys                ↭⟨ ≋⇒↭ ys=zs++y++ws ⟩
        zs ++ [ y ] ++ ws ↭⟨ shift (≈-sym x=y) zs ws ⟩
        x ∷ zs ++ ws ∎
