open import Data.Nat using (ℕ; _≟_; _+_; _≤_)
open import Data.Nat.Properties using (_<?_; m≤m+n; ≤-refl; ≤-trans)
open import Data.Fin using (fromℕ≤)
open import Data.Bool as 𝔹 using (Bool; _∧_; _∨_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; inspect; [_])
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.SimplePath.NonEmpty.Relation.Equality using (≈ₚ-sym)
open import RoutingLib.Data.SimplePath.NonEmpty.Properties using (∉-resp-≈ₚ) renaming (_∈?_ to _∈ₚ?_)

import RoutingLib.Routing.Models.BGPLite.Route as Routes
import RoutingLib.Routing.Models.BGPLite.Route.Properties as RouteProperties
open import RoutingLib.Routing.Models.BGPLite.Communities

module RoutingLib.Routing.Models.BGPLite.Policy (n : ℕ) where

  open Routes n
  open RouteProperties n
  
  data RoutePredicate : Set where
    true    : RoutePredicate
    false   : RoutePredicate
    and     : RoutePredicate → RoutePredicate → RoutePredicate
    or      : RoutePredicate → RoutePredicate → RoutePredicate
    not     : RoutePredicate → RoutePredicate
    inPath  : (i : ℕ)        → RoutePredicate
    inComm  : (c : Community) → RoutePredicate
    isLevel : (l : Level)     → RoutePredicate

  interpret : RoutePredicate → Route → Bool
  interpret true        _ = 𝔹.true
  interpret false       _ = 𝔹.false
  interpret (and s t)   r = interpret s r ∧ interpret t r
  interpret (or  s t)   r = interpret s r ∨ interpret t r
  interpret (not s)     r = 𝔹.not (interpret s r)
  interpret _           invalid = 𝔹.false
  interpret (inComm  c) (route l cs p) = c ∈? cs
  interpret (isLevel k) (route l cs p) = ⌊ k ≟ l ⌋
  interpret (inPath  i) (route l cs p) with i <? n
  ... | no  _   = 𝔹.false
  ... | yes i<n = ⌊ fromℕ≤ i<n ∈ₚ? p ⌋

  interpret-cong : ∀ p {r s} → r ≈ᵣ s → interpret p r ≡ interpret p s
  interpret-cong true        r≈s = refl
  interpret-cong false       r≈s = refl
  interpret-cong (and p q)   r≈s = cong₂ _∧_ (interpret-cong p r≈s) (interpret-cong q r≈s)
  interpret-cong (or  p q)   r≈s = cong₂ _∨_ (interpret-cong p r≈s) (interpret-cong q r≈s)
  interpret-cong (not p)     r≈s = cong 𝔹.not (interpret-cong p r≈s)
  interpret-cong (inPath  i) invalidEq = refl
  interpret-cong (inComm  c) invalidEq = refl
  interpret-cong (isLevel l) invalidEq = refl
  interpret-cong (inComm  c) (routeEq _ cs≈ds _)   = ∈-resp-≈ᶜˢ c cs≈ds
  interpret-cong (isLevel l) (routeEq refl _  _)   = refl
  interpret-cong (inPath  i) {route _ _ p} {route _ _ q} (routeEq _    _  p≈q) with i <? n
  ... | no _    = refl
  ... | yes i<n with fromℕ≤ i<n ∈ₚ? p | fromℕ≤ i<n ∈ₚ? q
  ...   | yes i∈p | yes i∈q = refl
  ...   | yes i∈p | no  i∉q = contradiction (i∈p ∘ (∉-resp-≈ₚ (≈ₚ-sym p≈q))) i∉q
  ...   | no  i∉p | yes i∈q = contradiction (i∈q ∘ ∉-resp-≈ₚ p≈q) i∉p
  ...   | no  i∉p | no  i∉q = refl
  
  ------------
  -- Policy --
  ------------
  
  data Policy : Set₁ where
    reject     : Policy
    cond       : RoutePredicate → Policy → Policy
    compose    : Policy → Policy → Policy
    raise      : ℕ → Policy
    addComm    : (c : Community) → Policy
    delComm    : (c : Community) → Policy

  apply : Policy → Route → Route
  apply _                   invalid        = invalid
  apply (raise x)           (route l cs p) = route (l + x) cs p
  apply (addComm c)         (route l cs p) = route l (add c cs) p
  apply (delComm c)         (route l cs p) = route l (remove c cs) p
  apply reject              r              = invalid
  apply (compose pol₂ pol₁) r              = apply pol₁ (apply pol₂ r )
  apply (cond p pol)        r              with interpret p r
  ... | 𝔹.true  = apply pol r
  ... | 𝔹.false = r

  apply-cong : ∀ pol {r s} → r ≈ᵣ s → apply pol r ≈ᵣ apply pol s
  apply-cong pol             invalidEq                = invalidEq
  apply-cong (raise x)       (routeEq refl cs≈ds p≈q) = routeEq refl cs≈ds p≈q
  apply-cong (addComm c)     (routeEq k≡l cs≈ds p≈q)  = routeEq k≡l (add-cong c cs≈ds) p≈q
  apply-cong (delComm c)     (routeEq k≡l cs≈ds p≈q)  = routeEq k≡l (remove-cong c cs≈ds) p≈q
  apply-cong reject          (routeEq _   _     _)    = invalidEq
  apply-cong (compose p₂ p₁) (routeEq k≡l cs≈ds p≈q)  = apply-cong p₁ (apply-cong p₂ (routeEq k≡l cs≈ds p≈q))
  apply-cong (cond P? pol)    {r@(route k cs p)} {s@(route l ds q)} r≈s@(routeEq k≡l cs≈ds p≈q)
    with interpret P? r | interpret P? s | inspect (interpret P?) r | inspect (interpret P?) s
  ... | 𝔹.true  | 𝔹.true  | _        | _        = apply-cong pol r≈s
  ... | 𝔹.true  | 𝔹.false | [ Pr≡t ] | [ Ps≡f ] =
    contradiction (trans (trans (sym Pr≡t) (interpret-cong P? r≈s)) Ps≡f) λ()
  ... | 𝔹.false | 𝔹.true  | [ Pr≡f ] | [ Ps≡t ] =
    contradiction (trans (trans (sym Ps≡t) (sym (interpret-cong P? r≈s))) Pr≡f) λ()
  ... | 𝔹.false | 𝔹.false | _        | _        = r≈s
  
  apply-levelIncr : ∀ pol {l cs p k ds q} → apply pol (route l cs p) ≈ᵣ route k ds q → l ≤ k
  apply-levelIncr reject              ()
  apply-levelIncr (raise x)           (routeEq refl _ _) = m≤m+n _ x
  apply-levelIncr (addComm c)         (routeEq refl _ _) = ≤-refl
  apply-levelIncr (delComm c)         (routeEq refl _ _) = ≤-refl
  apply-levelIncr (compose pol₂ pol₁)  {l} {cs} {p} eq
    with apply pol₂ (route l cs p) | inspect (apply pol₂) (route l cs p)
  ... | invalid      | _         = contradiction eq λ()
  ... | route m ds r | [ app≡u ] =
    ≤-trans (apply-levelIncr pol₂ (≈ᵣ-reflexive app≡u)) (apply-levelIncr pol₁ eq)
  apply-levelIncr (cond P? pol) {l} {cs} {p} eq with interpret P? (route l cs p)
  ... | 𝔹.true  = apply-levelIncr pol eq
  ... | 𝔹.false with eq
  ...   | routeEq refl _ _ = ≤-refl

  apply-trans : ∀ pol {x y r s} → r ≈ᵣ s → apply pol r ≡ x → apply pol s ≡ y → x ≈ᵣ y
  apply-trans pol r≈s refl refl = apply-cong pol r≈s
