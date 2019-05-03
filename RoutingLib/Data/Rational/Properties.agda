

module RoutingLib.Data.Rational.Properties where

import Data.Integer as ℤ
import Data.Integer.Properties as ℤₚ
open import Data.Product using (_,_)
open import Data.Rational
open import Data.Rational.Properties
open import Function using (_∘_)
open import Level using (0ℓ)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Relation.Nullary.Decidable as Dec

import RoutingLib.Data.Integer.Properties as ℤₚ
open import RoutingLib.Data.Rational

open import Algebra.FunctionProperties {A = ℚ} _≡_

drop-*<* : ∀ {p q} → p < q → (↥ p ℤ.* ↧ q) ℤ.< (↥ q ℤ.* ↧ p)
drop-*<* (*<* pq<qp) = pq<qp


<⇒≤ : _<_ ⇒ _≤_
<⇒≤ (*<* p<q) = *≤* (ℤₚ.<⇒≤ p<q)

<-irrefl : Irreflexive _≡_ _<_
<-irrefl refl (*<* p<p) = ℤₚ.<-irrefl refl p<p

<-asym : Asymmetric _<_
<-asym (*<* p<q) (*<* q<p) = ℤₚ.<-asym p<q q<p

<-trans : Transitive _<_
<-trans {p} {q} {r} (*<* p<q) (*<* q<r) = *<*
  (ℤₚ.*-cancelʳ-<-pos (↥ p ℤ.* ↧ r) (↥ r ℤ.* ↧ p) _ (begin-strict
  let n₁ = ↥ p; n₂ = ↥ q; n₃ = ↥ r; sd₁ = ↧ p; sd₂ = ↧ q; sd₃ = ↧ r in
  (n₁  ℤ.* sd₃) ℤ.* sd₂  ≡⟨ ℤₚ.*-assoc n₁ sd₃ sd₂ ⟩
  n₁   ℤ.* (sd₃ ℤ.* sd₂) ≡⟨ cong (n₁ ℤ.*_) (ℤₚ.*-comm sd₃ sd₂) ⟩
  n₁   ℤ.* (sd₂ ℤ.* sd₃) ≡⟨ sym (ℤₚ.*-assoc n₁ sd₂ sd₃) ⟩
  (n₁  ℤ.* sd₂) ℤ.* sd₃  <⟨ {!!} ⟩ -- ℤₚ.*-monoʳ-≤-pos ? ? ⟩
  (n₂  ℤ.* sd₁) ℤ.* sd₃  ≡⟨ cong (ℤ._* sd₃) (ℤₚ.*-comm n₂ sd₁) ⟩
  (sd₁ ℤ.* n₂)  ℤ.* sd₃  ≡⟨ ℤₚ.*-assoc sd₁ n₂ sd₃ ⟩
  sd₁  ℤ.* (n₂  ℤ.* sd₃) ≤⟨ {!!} ⟩ -- ℤₚ.*-monoˡ-≤-pos ? ? ⟩
  sd₁  ℤ.* (n₃  ℤ.* sd₂) ≡⟨ sym (ℤₚ.*-assoc sd₁ n₃ sd₂) ⟩
  (sd₁ ℤ.* n₃)  ℤ.* sd₂  ≡⟨ cong (ℤ._* sd₂) (ℤₚ.*-comm sd₁ n₃) ⟩
  (n₃  ℤ.* sd₁) ℤ.* sd₂  ∎))
  where open ℤₚ.≤-Reasoning
  
<-transˡ : Trans _<_ _≤_ _<_
<-transˡ = {!!}

<-transʳ : Trans _≤_ _<_ _<_
<-transʳ = {!!}

infix 4 _<?_

_<?_ : Decidable _<_
p <? q = Dec.map′ *<* drop-*<* ((↥ p ℤ.* ↧ q) ℤₚ.<? (↥ q ℤ.* ↧ p))

<-cmp : Trichotomous _≡_ _<_
<-cmp p q with ℤₚ.<-cmp (↥ p ℤ.* ↧ q) (↥ q ℤ.* ↧ p)
... | tri< < ≢ ≯ = tri< (*<* <)        (≢ ∘ ≡⇒≃) (≯ ∘ drop-*<*)
... | tri≈ ≮ ≡ ≯ = tri≈ (≮ ∘ drop-*<*) (≃⇒≡ ≡)   (≯ ∘ drop-*<*)
... | tri> ≮ ≢ > = tri> (≮ ∘ drop-*<*) (≢ ∘ ≡⇒≃) (*<* >)

<-irrelevant : Irrelevant _<_
<-irrelevant {p} {q} (*<* p<q₁) (*<* p<q₂) = cong *<* (ℤₚ.<-irrelevant {x = ↥ p ℤ.* ↧ q} p<q₁ p<q₂)

<-respʳ-≡ : _<_ Respectsʳ _≡_
<-respʳ-≡ = subst (_ <_)

<-respˡ-≡ : _<_ Respectsˡ _≡_
<-respˡ-≡ = subst (_< _)

<-resp-≡ : _<_ Respects₂ _≡_
<-resp-≡ = <-respʳ-≡ , <-respˡ-≡

<-isStrictPartialOrder : IsStrictPartialOrder _≡_ _<_
<-isStrictPartialOrder = record
  { isEquivalence = isEquivalence
  ; irrefl        = <-irrefl
  ; trans         = <-trans
  ; <-resp-≈      = <-resp-≡
  }

<-isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_
<-isStrictTotalOrder = record
  { isEquivalence = isEquivalence
  ; trans         = <-trans
  ; compare       = <-cmp
  }

<-strictPartialOrder : StrictPartialOrder 0ℓ 0ℓ 0ℓ
<-strictPartialOrder = record
  { isStrictPartialOrder = <-isStrictPartialOrder
  }

<-strictTotalOrder : StrictTotalOrder 0ℓ 0ℓ 0ℓ
<-strictTotalOrder = record
  { isStrictTotalOrder = <-isStrictTotalOrder
  }
{-
------------------------------------------------------------------------
-- normalize

normalize′-coprime : ∀ {n d-1} {n≢0 : n ≢0} .(c : Coprime n (suc d-1)) →
                    normalize′ n (suc d-1) {n≢0} ≡ mkℚ (+ n) d-1 c
normalize′-coprime {suc n} {d-1} c with gcd (suc n) (suc d-1)
... | zero  , GCD.is (1+m∣0 , _) _ = contradiction (0∣⇒≡0 1+m∣0) λ()
... | suc g , G@(GCD.is (divides (suc p) refl , divides (suc q) refl) _)
  with GCD.unique G (C.coprime-gcd (recomputeCP c))
...   | refl = mkℚ-cong (cong +[1+_] (sym (ℕ.*-identityʳ p))) (sym (ℕ.*-identityʳ q))

------------------------------------------------------------------------
-- _/_ 

/-cong : ∀ {n₁ d₁ n₂ d₂} {d₁≢0 : d₁ ≢0} {d₂≢0 : d₂ ≢0} →
         n₁ ≡ n₂ → d₁ ≡ d₂ → _/_ n₁ d₁ {d₁≢0} ≡ _/_ n₂ d₂ {d₂≢0}
/-cong refl refl = refl

↥p/↧p≡p : ∀ p → ↥ p / ↧ₙ p ≡ p
↥p/↧p≡p (mkℚ +0       d-1 prf) = mkℚ-cong refl (sym (ℕ.suc-injective (C.0-coprimeTo-m⇒m≡1 (recomputeCP prf))))
↥p/↧p≡p (mkℚ +[1+ n ] d-1 prf) = normalize′-coprime prf
↥p/↧p≡p (mkℚ -[1+ n ] d-1 prf) = cong (-_) (normalize′-coprime prf)

------------------------------------------------------------------------
-- _*_ 


postulate *-identityʳ : RightIdentity 1ℚ _*_
-- *-identityʳ x = {!!}

postulate *-identityˡ : LeftIdentity 1ℚ _*_
-- *-identityˡ x = {!!}

*-identity : Identity 1ℚ _*_
*-identity = *-identityˡ , *-identityʳ

------------------------------------------------------------------------
-- _⊔_

postulate p⊔q≤p+q : ∀ p q → p ⊔ q ≤ p + q

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
