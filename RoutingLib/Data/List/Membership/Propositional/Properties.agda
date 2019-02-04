open import Algebra.FunctionProperties using (Op₂; Selective)
open import Data.Nat using (ℕ; suc; zero; _<_; _≤_; s≤s; z≤n; _≟_)
open import Data.Nat.Properties using (⊔-sel; m≤m⊔n; ≤∧≢⇒<; ⊔-identityʳ; n≤m⊔n; ≤-trans)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List
open import Data.List.Any as Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Permutation.Inductive using (_↭_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃; _,_; _×_; proj₂)
open import Relation.Binary using (Setoid; Decidable; DecSetoid)
open import Relation.Binary.PropositionalEquality using (_≡_; setoid; refl; cong; cong₂)
open import Relation.Binary.List.Pointwise using (≡⇒Rel≡)
open import Relation.Nullary using (yes; no)
open import Relation.Unary using () renaming (Decidable to Decidableᵤ)
open import Function using (_∘_; id)

open import RoutingLib.Data.List using (combine; allFinPairs)
open import RoutingLib.Data.Nat.Properties using (ℕₛ)
import RoutingLib.Data.List.Membership.Setoid as SetoidMembership
open import RoutingLib.Data.List.Relation.Permutation.Inductive using (↭-pres-∈)

module RoutingLib.Data.List.Membership.Propositional.Properties where

  import RoutingLib.Data.List.Membership.Setoid.Properties as GM
  import Data.List.Membership.Propositional.Properties as GM2

  ∈-combine⁺ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
              {u v xs ys} (f : A → B → C) → u ∈ xs → v ∈ ys →
              f u v ∈ combine f xs ys
  ∈-combine⁺ f = GM.∈-combine (setoid _) (setoid _) (setoid _) (cong₂ f)

  ∈-upTo⁺ : ∀ {n i} → i < n → i ∈ upTo n
  ∈-upTo⁺ = GM2.∈-applyUpTo⁺ id

  ∈-applyDownFrom⁺ : ∀ {a} {A : Set a} (f : ℕ → A) {n i} →
                     i < n → f i ∈ applyDownFrom f n
  ∈-applyDownFrom⁺ f {suc n} {i} (s≤s i≤n) with i ≟ n
  ... | yes i≡n = here (cong f i≡n)
  ... | no  i≢n = there (∈-applyDownFrom⁺ f (≤∧≢⇒< i≤n i≢n))

  ∈-downFrom⁺ : ∀ {n i} → i < n → i ∈ downFrom n
  ∈-downFrom⁺ i<n = ∈-applyDownFrom⁺ id i<n

  {-
  ∈-applyBetween⁺ : ∀ {a} {A : Set a} (f : ℕ → A) {s e i} →
                    s ≤ i → i < e → f i ∈ applyBetween f s e
  ∈-applyBetween⁺ = GM.∈-applyBetween⁺ (setoid _)

  ∈-applyBetween⁻ : ∀ {a} {A : Set a} (f : ℕ → A) s e {v} →
                    v ∈ applyBetween f s e → ∃ λ i → s ≤ i × i < e × v ≡ f i
  ∈-applyBetween⁻ = GM.∈-applyBetween⁻ (setoid _)


  ∈-between⁺ : ∀ {s e i} → s ≤ i → i < e → i ∈ between s e
  ∈-between⁺ = ∈-applyBetween⁺ id

  ∈-between⁻ : ∀ s e {i} → i ∈ between s e → s ≤ i × i < e
  ∈-between⁻ s e i∈ with ∈-applyBetween⁻ id s e i∈
  ... | i , s≤i , i<e , refl = s≤i , i<e
  -}

  ∈-allFin⁺ : ∀ {n} i → i ∈ allFin n
  ∈-allFin⁺ = GM2.∈-tabulate⁺

  ∈-allFinPairs⁺ : ∀ {n} i j → (i , j) ∈ allFinPairs n
  ∈-allFinPairs⁺ i j = ∈-combine⁺ _,_ (∈-allFin⁺ i) (∈-allFin⁺ j)



  ∈-perm : ∀ {a} {A : Set a} {x : A} {xs ys} → xs ↭ ys → x ∈ xs → x ∈ ys
  ∈-perm = ↭-pres-∈ (setoid _) --GM.∈-perm (setoid _)
