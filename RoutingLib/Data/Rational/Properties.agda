

module RoutingLib.Data.Rational.Properties where

open import Data.Nat as ℕ using (zero; suc)
import Data.Nat.Properties as ℕₚ
open import Data.Nat.GCD
open import Data.Nat.Coprimality as C using (Coprime; coprime?; coprime-gcd; gcd-coprime)
open import Data.Nat.Divisibility using (divides; 0∣⇒≡0)
open import Data.Integer as ℤ using (+_; -[1+_])
import Data.Integer.Properties as ℤₚ
open import Data.Product using (∃; _×_; _,_)
open import Data.Rational
open import Data.Rational.Properties
open import Function using (_∘_)
open import Level using (0ℓ)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Rational

open import Algebra.FunctionProperties {A = ℚ} _≡_

mkℚ-cong : ∀ {n₁ n₂ d₁ d₂}
           .{c₁ : Coprime ℤ.∣ n₁ ∣ (suc d₁)}
           .{c₂ : Coprime ℤ.∣ n₂ ∣ (suc d₂)} →
           n₁ ≡ n₂ → d₁ ≡ d₂ → mkℚ n₁ d₁ c₁ ≡ mkℚ n₂ d₂ c₂
mkℚ-cong refl refl = refl



------------------------------------------------------------------------
-- normalize

private
  recomputeCP : ∀ {n d} → .(Coprime n d) → Coprime n d
  recomputeCP n d = {!!}
  
normalize-coprime : ∀ {n d-1} {n≢0 : n ≢0} .(c : Coprime n (suc d-1)) →
                    normalize n (suc d-1) {n≢0} ≡ mkℚ (+ n) d-1 c
normalize-coprime {suc n} {d-1} c with gcd (suc n) (suc d-1)
... | zero  , GCD.is (1+m∣0 , _) _ = contradiction (0∣⇒≡0 1+m∣0) λ()
... | suc g , G@(GCD.is (divides (suc p) refl , divides (suc q) refl) _)
  with GCD.unique G (coprime-gcd (recomputeCP c))
...   | refl = mkℚ-cong
  (cong +[1+_] (sym (ℕₚ.*-identityʳ p)))
  (sym (ℕₚ.*-identityʳ q))

------------------------------------------------------------------------
-- _/_ 

/-cong : ∀ {n₁ d₁ n₂ d₂} {d₁≢0 : d₁ ≢0} {d₂≢0 : d₂ ≢0} →
         n₁ ≡ n₂ → d₁ ≡ d₂ → _/_ n₁ d₁ {d₁≢0} ≡ _/_ n₂ d₂ {d₂≢0}
/-cong refl refl = refl

/-normalizes : ∀ n d → ∃ λ c → ↥ (n / d) ≡ + c ℤ.* n × ↧ (n / d) ≡ + c ℤ.* + d
/-normalizes = {!!}

↥p/↧p≡p : ∀ p → ↥ p / ↧ₙ p ≡ p
↥p/↧p≡p (mkℚ +0       d-1 prf) = mkℚ-cong refl (sym (ℕₚ.suc-injective (C.0-coprimeTo-m⇒m≡1 (recomputeCP prf))))
↥p/↧p≡p (mkℚ +[1+ n ] d-1 prf) = normalize-coprime prf
↥p/↧p≡p (mkℚ -[1+ n ] d-1 prf) = cong (-_) (normalize-coprime prf)

↥↧-cong : ∀ {p q} → ↥ p ≡ ↥ q → ↧ p ≡ ↧ q → p ≡ q
↥↧-cong refl refl = refl

{-
------------------------------------------------------------------------
-- _*_ 

postulate *-identityʳ : RightIdentity 1ℚ _*_
-- *-identityʳ x = {!!}

postulate *-identityˡ : LeftIdentity 1ℚ _*_
-- *-identityˡ x = {!!}

*-identity : Identity 1ℚ _*_
*-identity = *-identityˡ , *-identityʳ
-}

------------------------------------------------------------------------
-- _+_

+-normalizes : ∀ p q → ∃ λ c → ↥ (p + q) ≡ + c ℤ.* (↥ p ℤ.* ↧ q ℤ.+ ↥ q ℤ.* ↧ p)
                             × ↧ (p + q) ≡ + c ℤ.* (↧ p ℤ.* ↧ q)
+-normalizes p q = /-normalizes (↥ p ℤ.* ↧ q ℤ.+ ↥ q ℤ.* ↧ p) (↧ₙ p ℕ.* ↧ₙ q)

+-assoc : Associative _+_
+-assoc p q r = ↥↧-cong +-assoc-↥ +-assoc-↧
  where
  +-assoc-↥ : ↥ ((p + q) + r) ≡ ↥ (p + (q + r))
  +-assoc-↥ = {!!}

  +-assoc-↧ : ↧ ((p + q) + r) ≡ ↧ (p + (q + r))
  +-assoc-↧ = {!!}
  
+-comm : Commutative _+_
+-comm p q = /-cong (ℤₚ.+-comm (↥ p ℤ.* ↧ q) _) (ℕₚ.*-comm (↧ₙ p) (↧ₙ q))

p≤p+q : ∀ p q → p ≤ p + q
p≤p+q p q with +-normalizes p q
... | c , ↥pq≡c[pq+qp] , ↧pq≡cpq = *≤* (begin
  ↥ p ℤ.* ↧ (p + q)                               ≡⟨ cong (↥ p ℤ.*_) ↧pq≡cpq ⟩
  ↥ p ℤ.* (+ c ℤ.* (↧ p ℤ.* ↧ q))                 ≡⟨ {!!} ⟩
  (+ c ℤ.* ↧ p) ℤ.* (↥ p ℤ.* ↧ q)                 ≤⟨ {!!} ⟩ --ℤₚ.*-monoˡ-≤-non-neg ? {!!} ⟩
  (+ c ℤ.* ↧ p) ℤ.* (↥ p ℤ.* ↧ q ℤ.+ ↥ q ℤ.* ↧ p) ≡⟨ {!!} ⟩
  (+ c ℤ.* (↥ p ℤ.* ↧ q ℤ.+ ↥ q ℤ.* ↧ p)) ℤ.* ↧ p ≡⟨ cong (ℤ._* ↧ p) (sym ↥pq≡c[pq+qp]) ⟩
  (↥ (p + q))                           ℤ.* ↧ p   ∎)
  where open ℤₚ.≤-Reasoning

p≤q+p : ∀ p q → p ≤ q + p
p≤q+p p q = subst (p ≤_) (+-comm p q) (p≤p+q p q)

------------------------------------------------------------------------
-- _*_

*-normalizes : ∀ p q → ∃ λ c → ↥ (p * q) ≡ + c ℤ.* (↥ p ℤ.* ↥ q)
                             × ↧ (p * q) ≡ + c ℤ.* (↧ p ℤ.* ↧ q)
*-normalizes p q = {!!} --/-normalizes (↥ p ℤ.* ↥ q) (↧ₙ p ℕ.* ↧ₙ q)

*-assoc : Associative _*_
*-assoc p q r with *-normalizes (p * q) r | *-normalizes p q
... | c , ↥pqr≡cpqr , ↧pqr≡cpqr | d , ↥pq≡dpq , ↧pq≡dpq = ↥↧-cong *-assoc-↥ *-assoc-↧
  where
  *-assoc-↥ : ↥ ((p * q) * r) ≡ ↥ (p * (q * r))
  *-assoc-↥ = begin-equality
    ↥ ((p * q) * r)                         ≡⟨ ↥pqr≡cpqr ⟩
    + c ℤ.* (↥ (p * q) ℤ.* ↥ r)             ≡⟨ {!!} ⟩
    + c ℤ.* (+ d ℤ.* (↥ p ℤ.* ↥ q) ℤ.* ↥ r) ≡⟨ {!!} ⟩
    ↥ (p * (q * r))                         ∎
    where open ℤₚ.≤-Reasoning
    
  *-assoc-↧ : ↧ ((p * q) * r) ≡ ↧ (p * (q * r))
  *-assoc-↧ = {!!}

------------------------------------------------------------------------
-- _⊔_

p⊔q≤p+q : ∀ p q → p ⊔ q ≤ p + q
p⊔q≤p+q p q with (↥ p ℤ.* ↧ q) ℤ.≤? (↥ q ℤ.* ↧ p)
... | yes _ = p≤q+p q p
... | no  _ = p≤p+q p q

{-
------------------------------------------------------------------------
-- A module for reasoning about the _≤_ and _<_ relations

module ≤-Reasoning where
  open import Relation.Binary.Reasoning.Base.Triple
    ≤-isPreorder
    <-trans
    (resp₂ _<_)
    <⇒≤
    <-transˡ
    <-transʳ
    public
    hiding (_≈⟨_⟩_; _≈˘⟨_⟩_)
-}
