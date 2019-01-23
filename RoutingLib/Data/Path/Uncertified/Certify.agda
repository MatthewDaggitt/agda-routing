open import Data.Fin using (Fin; toℕ; fromℕ≤)
open import Data.Fin.Properties using (toℕ<n; toℕ-injective; toℕ-fromℕ≤; fromℕ≤-toℕ)
open import Data.List.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Properties using (_<?_)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (inj₁)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong; cong₂)

open import RoutingLib.Data.Fin.Properties using (fromℕ≤-injective; fromℕ≤-cong)

open import RoutingLib.Data.Path.Certified
open import RoutingLib.Data.Path.Certified.Properties
open import RoutingLib.Data.Path.Uncertified as U using ([]; _∷_; left; right)
open import RoutingLib.Data.Path.Uncertified.Properties as Uₚ

module RoutingLib.Data.Path.Uncertified.Certify {n : ℕ} where

private

  help₁ : ∀ {i j} {i' j' : Fin n} → toℕ i' ≡ i → toℕ j' ≡ j → i ≢ j → i' ≢ j'
  help₁ i≡i j≡j i≢j refl = i≢j (trans (sym i≡i) j≡j)

  help₂ : ∀ {i} {i' : Fin n} (i<n : i < n) → toℕ i' ≡ i → i' ≡ fromℕ≤ i<n
  help₂ i<n eq = toℕ-injective (trans eq (sym (toℕ-fromℕ≤ i<n)))

mutual

  certify : U.Path → Path n
  certify []            = []
  certify ((i , j) ∷ p) with i Uₚ.∈ₚ? p | (i , j) Uₚ.⇿? p | i <? n | j <? n
  ... | yes _   | _        | _       | _       = []
  ... | no  _   | no  _    | _       | _       = []
  ... | no  _   | yes _    | no  _   | _       = []
  ... | no  _   | yes _    | yes _   | no  _   = []
  ... | no  i∉p | yes ij⇿p | yes i<n | yes j<n =
    (fromℕ≤ i<n , fromℕ≤ j<n) ∷ certify p ∣ ⇿-certify⁺ (toℕ-fromℕ≤ i<n) (toℕ-fromℕ≤ j<n) ij⇿p ∣ ∉ₚ-certify⁺ (toℕ-fromℕ≤ i<n) i∉p

  ⇿-certify⁺ : ∀ {p i j i' j'} → toℕ i' ≡ i → toℕ j' ≡ j → (i , j) U.⇿ p → (i' , j') ⇿ certify p
  ⇿-certify⁺ {[]}          i≡i j≡j (U.start    i≢j) = start (help₁ i≡i j≡j i≢j)
  ⇿-certify⁺ {(j , k) ∷ p} i≡i j≡j (U.continue i≢j) with j Uₚ.∈ₚ? p | (j , k) Uₚ.⇿? p | j <? n | k <? n
  ... | yes _ | _     | _        | _     = start (help₁ i≡i j≡j i≢j)
  ... | no  _ | no  _ | _        | _     = start (help₁ i≡i j≡j i≢j)
  ... | no  _ | yes _ | no _     | _     = start (help₁ i≡i j≡j i≢j)
  ... | no  _ | yes _ | yes _    | no _  = start (help₁ i≡i j≡j i≢j)
  ... | no  _ | yes _ | yes j<n' | yes _ rewrite help₂ j<n' j≡j = continue (help₁ i≡i (toℕ-fromℕ≤ j<n') i≢j)


  ∉ₚ-certify⁺ : ∀ {p k k'} → toℕ k' ≡ k → k U.∉ₚ p → k' ∉ₚ certify p
  ∉ₚ-certify⁺ {[]}          k≡k k∉p = notThere
  ∉ₚ-certify⁺ {(i , j) ∷ p} k≡k k∉p with i Uₚ.∈ₚ? p | (i , j) Uₚ.⇿? p | i <? n | j <? n
  ... | yes _ | _     | _       | _       = notThere
  ... | no  _ | no  _ | _       | _       = notThere
  ... | no  _ | yes _ | no  _   | _       = notThere
  ... | no  _ | yes _ | yes _   | no  _   = notThere
  ... | no  _ | yes _ | yes i<n | yes j<n = notHere
    (k∉p ∘ (λ { refl → here (subst (U._∈ₑ _) (trans (sym (toℕ-fromℕ≤ i<n)) k≡k) left)}))
    (k∉p ∘ (λ { refl → here (subst (U._∈ₑ _) (trans (sym (toℕ-fromℕ≤ j<n)) k≡k) right)}))
    (∉ₚ-certify⁺ k≡k (k∉p ∘ there))

  ∈ₚ-certify⁻ : ∀ {p k k'} → toℕ k' ≡ k → k' ∈ₚ certify p → k U.∈ₚ p
  ∈ₚ-certify⁻ {[]}          {_} k≡k  k∈pᶜ = contradiction notThere k∈pᶜ
  ∈ₚ-certify⁻ {(i , j) ∷ p} {k} refl k∈pᶜ with i Uₚ.∈ₚ? p | (i , j) Uₚ.⇿? p | i <? n | j <? n
  ... | yes _ | _     | _       | _       = contradiction notThere k∈pᶜ
  ... | no  _ | no  _ | _       | _       = contradiction notThere k∈pᶜ
  ... | no  _ | yes _ | no  _   | _       = contradiction notThere k∈pᶜ
  ... | no  _ | yes _ | yes _   | no  _   = contradiction notThere k∈pᶜ
  ... | no  _ | yes _ | yes i<n | yes j<n with k Uₚ.∈ₑ? (i  , j)
  ...   | yes k∈ij = here k∈ij
  ...   | no  k∉ij = there (∈ₚ-certify⁻ refl (k∈pᶜ ∘ notHere
    (k∉ij ∘ λ { refl → subst (U._∈ₑ _) (sym (toℕ-fromℕ≤ i<n)) left })
    ((k∉ij ∘ λ { refl → subst (U._∈ₑ _) (sym (toℕ-fromℕ≤ j<n)) right }))))

  certify-accept : ∀ {i j p} (ij⇿p : (toℕ i , toℕ j) U.⇿ p) (i∉p : toℕ i U.∉ₚ p) →
                   certify ((toℕ i , toℕ j) ∷ p) ≈ₚ (i , j) ∷ certify p ∣ ⇿-certify⁺ refl refl ij⇿p ∣ ∉ₚ-certify⁺ refl i∉p
  certify-accept {i} {j} {p} ij⇿p i∉p with toℕ i Uₚ.∈ₚ? p | (toℕ i , toℕ j) Uₚ.⇿? p | toℕ i <? n | toℕ j <? n
  ... | yes i∈p | _        | _       | _       = contradiction i∈p i∉p
  ... | no  _   | no ¬ij⇿p | _       | _       = contradiction ij⇿p ¬ij⇿p
  ... | no  _   | yes _    | no  i≮n | _       = contradiction (toℕ<n i) i≮n
  ... | no  _   | yes _    | yes _   | no  j≮n = contradiction (toℕ<n j) j≮n
  ... | no  _   | yes _    | yes i<n | yes j<n = cong₂ _,_ (fromℕ≤-toℕ i i<n) (fromℕ≤-toℕ j j<n) ∷ ≈ₚ-refl
