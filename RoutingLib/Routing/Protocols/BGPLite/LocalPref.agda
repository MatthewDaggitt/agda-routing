open import Data.Fin.Base as Fin hiding (_-_)
open import Data.Bool using (Bool)
import Data.Fin.Properties as Fin
open import Data.Nat using (ℕ; zero; suc; _^_; _∸_)
open import Data.Nat.Properties as Nat
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Level

import RoutingLib.Data.Fin.Induction as Fin

module RoutingLib.Routing.Protocols.BGPLite.LocalPref where

private
  n = 2 ^ 8

LocalPref : Set
LocalPref = Fin n

2⁸-1 : LocalPref
2⁸-1 = fromℕ (n ∸ 1)

_≟ˡᵖ_ : DecidableEquality LocalPref
_≟ˡᵖ_ = Fin._≟_

_≤ˡᵖ_ : Rel LocalPref 0ℓ
_≤ˡᵖ_ = Fin._≤_

_<ˡᵖ_ : Rel LocalPref 0ℓ
_<ˡᵖ_ = Fin._<_

≤ˡᵖ-isDecTotalOrder : IsDecTotalOrder _≡_ _≤ˡᵖ_
≤ˡᵖ-isDecTotalOrder = Fin.≤-isDecTotalOrder

open IsDecTotalOrder ≤ˡᵖ-isDecTotalOrder public
  using () renaming
  ( refl      to ≤ˡᵖ-refl
  ; reflexive to ≤ˡᵖ-reflexive
  ; antisym   to ≤ˡᵖ-antisym
  ; trans     to ≤ˡᵖ-trans
  ; total     to ≤ˡᵖ-total
  )

<ˡᵖ-isStrictTotalOrder : IsStrictTotalOrder _≡_ _<ˡᵖ_
<ˡᵖ-isStrictTotalOrder = Fin.<-isStrictTotalOrder

open IsStrictTotalOrder <ˡᵖ-isStrictTotalOrder public
  using () renaming
  ( irrefl    to <ˡᵖ-irrefl
  ; trans     to <ˡᵖ-trans
  ; asym      to <ˡᵖ-asym
  ; compare   to <ˡᵖ-compare
  )

≤ˡᵖ-max : ∀ l → l ≤ˡᵖ 2⁸-1
≤ˡᵖ-max l = Fin.toℕ≤pred[n] l
  
_≥ˡᵖ_ : Rel LocalPref 0ℓ
x ≥ˡᵖ y = y ≤ˡᵖ x

_>ˡᵖ_ : Rel LocalPref 0ℓ
x >ˡᵖ y = y <ˡᵖ x

_-_ : LocalPref → ℕ → LocalPref
l     - zero  = l
zero  - _     = Fin.zero
suc l - suc x = inject₁ l - x

l-x≤l : ∀ l x → l - x ≤ l
l-x≤l l       zero    = ≤ˡᵖ-refl
l-x≤l zero    (suc x) = ≤ˡᵖ-refl
l-x≤l (suc l) (suc x) = Nat.≤-step (≤-trans (l-x≤l (inject₁ l) x) (≤-reflexive (Fin.toℕ-inject₁ l)))
