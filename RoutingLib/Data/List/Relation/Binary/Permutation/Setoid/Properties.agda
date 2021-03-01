open import Data.List hiding (head; tail)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there; _─_)
open import Data.List.Relation.Unary.All using (All; []; _∷_; here; there)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using (head; tail; Pointwise-length)
open import Data.List.Properties using (∷-injective; ∷-injectiveʳ; ∷-injectiveˡ)
open import Data.Fin using (Fin; zero; suc; cast)
open import Data.Fin.Properties as Fin using (suc-injective)
open import Data.Fin.Patterns
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; s≤s; z≤n)
open import Data.Nat.Properties as ℕ
open import Data.Nat.Induction
open import Data.Product using (_×_; ∃; ∃₂; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Function using (id; _∘_; flip; const; Injective)
open import Level using (_⊔_)
open import Relation.Unary using (Pred) renaming (Decidable to Decidable₁)
open import Relation.Binary
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction; contraposition)
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_)

open import RoutingLib.Data.List
open import RoutingLib.Data.Nat.Properties
open import RoutingLib.Data.Fin.Properties using (cast-injective)

import Data.List.Membership.Setoid as Membership
import Data.List.Membership.DecSetoid as DecMembership
import Data.List.Membership.Setoid.Properties as Membershipₚ
import Data.List.Relation.Binary.Equality.Setoid as Equality
import Data.List.Relation.Binary.Permutation.Setoid as PermutationSetoid
import Data.List.Relation.Binary.Permutation.Setoid.Properties as PermutationSetoidProperties
import Data.List.Relation.Unary.Unique.Setoid as Unique

open import RoutingLib.Data.List.Relation.Binary.Pointwise using (lookup⁺)
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

private
  variable
    xs ys : List A

pattern 1+ i = suc i
pattern 2+ i = suc (suc i)

permute : xs ↭ ys → Fin (length xs) → Fin (length ys)
permute (refl ≋)      i             = cast (Pointwise-length ≋) i
permute (prep _ _)    zero          = zero
permute (prep _ ↭₁)   (suc i)       = suc (permute ↭₁ i)
permute (swap _ _ _)  zero          = suc zero
permute (swap _ _ _)  (suc zero)    = zero
permute (swap _ _ ↭₁) (suc (suc i)) = suc (suc (permute ↭₁ i))
permute (trans ↭₁ ↭₂)               = permute ↭₂ ∘ permute ↭₁

permute-lookup : ∀ (xs↭ys : xs ↭ ys) → ∀ i → lookup xs i ≈ lookup ys (permute xs↭ys i)
permute-lookup (refl xs≋ys)        i             = lookup⁺ xs≋ys i
permute-lookup (prep eq xs↭ys)     zero          = eq
permute-lookup (prep _  xs↭ys)     (suc i)       = permute-lookup xs↭ys i
permute-lookup (swap eq _ xs↭ys)   zero          = eq
permute-lookup (swap _ eq xs↭ys)   (suc zero)    = eq
permute-lookup (swap _ _  xs↭ys)   (suc (suc i)) = permute-lookup xs↭ys i
permute-lookup (trans xs↭ys ys↭zs) i             = Eq.trans (permute-lookup xs↭ys i) (permute-lookup ys↭zs _)

permute-injective : ∀ (xs↭ys : xs ↭ ys) → Injective _≡_ _≡_ (permute xs↭ys)
permute-injective (refl ≋)                    = cast-injective (Pointwise-length ≋)
permute-injective (prep _ _)    {0F}   {0F}   = const P.refl
permute-injective (prep _ ↭₁)   {1+ i} {1+ j} = P.cong suc ∘ permute-injective ↭₁ ∘ Fin.suc-injective
permute-injective (swap _ _ _)  {0F}   {0F}   = const P.refl
permute-injective (swap _ _ _)  {0F}   {1F}   ()
permute-injective (swap _ _ _)  {0F}   {2+ j} ()
permute-injective (swap _ _ _)  {1F}   {0F}   ()
permute-injective (swap _ _ _)  {1F}   {1F}   = const P.refl
permute-injective (swap _ _ _)  {1F}   {2+ j} ()
permute-injective (swap _ _ ↭₁) {2+ i} {2+ j} = P.cong (Fin.suc ∘ suc) ∘ permute-injective ↭₁ ∘ Fin.suc-injective ∘ Fin.suc-injective
permute-injective (trans ↭₁ ↭₂) {i}           = permute-injective ↭₁ ∘ permute-injective ↭₂

xs↭ys⇒|xs|≡|ys| : ∀ {xs ys} → xs ↭ ys → length xs ≡ length ys
xs↭ys⇒|xs|≡|ys| (refl eq)            = Pointwise-length eq
xs↭ys⇒|xs|≡|ys| (prep eq xs↭ys)      = P.cong suc (xs↭ys⇒|xs|≡|ys| xs↭ys)
xs↭ys⇒|xs|≡|ys| (swap eq₁ eq₂ xs↭ys) = P.cong (λ x → suc (suc x)) (xs↭ys⇒|xs|≡|ys| xs↭ys)
xs↭ys⇒|xs|≡|ys| (trans xs↭ys xs↭ys₁) = P.trans (xs↭ys⇒|xs|≡|ys| xs↭ys) (xs↭ys⇒|xs|≡|ys| xs↭ys₁)

|xs|≢|ys|⇒¬xs↭ys : ∀ {xs ys} → length xs ≢ length ys → ¬ (xs ↭ ys)
|xs|≢|ys|⇒¬xs↭ys = contraposition xs↭ys⇒|xs|≡|ys|

¬[]↭x∷xs : ∀ x xs → ¬([] ↭ x ∷ xs)
¬[]↭x∷xs x xs = |xs|≢|ys|⇒¬xs↭ys λ()

¬x∷xs↭[] : ∀ x xs → ¬(x ∷ xs ↭ [])
¬x∷xs↭[] x xs = |xs|≢|ys|⇒¬xs↭ys λ()

tabulate⁺ : ∀ {n} {f g : Fin n → A} →
            (∀ {i} → f i ≈ g i) → tabulate f ↭ tabulate g
tabulate⁺ {zero}  f≈g = refl []
tabulate⁺ {suc k} f≈g = prep f≈g (tabulate⁺ {k} f≈g)

x∷xs↭ys⇒x∈ys : ∀ {x xs ys} → x ∷ xs ↭ ys → x ∈ ys
x∷xs↭ys⇒x∈ys (refl (x≈y ∷ _))      = here x≈y
x∷xs↭ys⇒x∈ys (prep x≈y _)          = here x≈y
x∷xs↭ys⇒x∈ys (swap x₁≈y₂ _ _)      = there (here x₁≈y₂)
x∷xs↭ys⇒x∈ys (trans x∷xs↭zs zs↭ys) = ∈-resp-↭ zs↭ys (x∷xs↭ys⇒x∈ys x∷xs↭zs)

∉-resp-↭ : ∀ {x} → (x ∉_) Respects _↭_
∉-resp-↭ xs↭ys = _∘ ∈-resp-↭ (↭-sym xs↭ys)

module _ (_≟_ : Decidable _≈_) where

  DS : DecSetoid a ℓ
  DS = record
    { isDecEquivalence = record
      { isEquivalence = ≈-isEquivalence
      ; _≟_           = _≟_
      }
    }

  open DecMembership DS using (_∈?_)
  open PermutationReasoning

  infix 3 _↭?_

  _↭?_ : Decidable _↭_
  []       ↭? []       = yes (refl [])
  []       ↭? (y ∷ ys) = no (¬[]↭x∷xs y ys)
  (x ∷ xs) ↭? ys       with x ∈? ys
  ... | no  x∉ys  = no (x∉ys ∘ x∷xs↭ys⇒x∈ys)
  ... | yes x∈ys with Membershipₚ.∈-∃++ S x∈ys
  ...   | zs , ws , y , x≈y , ys≋zs++y++ws with xs ↭? zs ++ ws
  ...     | yes xs↭zs++ws = yes (begin
    x ∷ xs            <⟨ xs↭zs++ws ⟩
    x ∷ (zs ++ ws)    ↭˘⟨ shift (≈-sym x≈y) zs ws ⟩
    zs ++ [ y ] ++ ws ≋˘⟨ ys≋zs++y++ws ⟩
    ys                ∎)
  ...     | no ¬xs↭zs++ws = no (¬xs↭zs++ws ∘ λ xs↭zs++ws → dropMiddleElement [] [] (begin
    x ∷ xs            ↭⟨ xs↭zs++ws ⟩
    ys                ≋⟨ ys≋zs++y++ws ⟩
    zs ++ [ y ] ++ ws ↭⟨ shift (≈-sym x≈y) zs ws ⟩
    x ∷ zs ++ ws      ∎))

  ↭-isDecEquivalence : IsDecEquivalence _↭_
  ↭-isDecEquivalence = record
    { isEquivalence = ↭-isEquivalence
    ; _≟_ = _↭?_
    }

  ↭-decSetoid : DecSetoid _ _
  ↭-decSetoid = record
    { isDecEquivalence = ↭-isDecEquivalence
    }
