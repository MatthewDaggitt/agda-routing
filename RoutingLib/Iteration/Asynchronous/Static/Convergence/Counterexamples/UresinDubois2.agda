--------------------------------------------------------------------------
-- A counter-example of Theorem 2 by Uresin & Dubois
--------------------------------------------------------------------------

module RoutingLib.Iteration.Asynchronous.Static.Convergence.Counterexamples.UresinDubois2 where

open import Data.Fin using (Fin; zero; suc; _≟_) renaming ( _≤_ to _≤F_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product
open import Level using (0ℓ; _⊔_) renaming (suc to lsuc)
import Relation.Binary as B
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Indexed.Homogeneous
open import Relation.Unary using (U)
open import Relation.Unary.Properties using (U-Universal)

open import RoutingLib.Data.Table using (Table)
open import RoutingLib.Relation.Unary.Indexed

open import RoutingLib.Iteration.Synchronous
open import RoutingLib.Iteration.Asynchronous.Static
open import RoutingLib.Iteration.Asynchronous.Static.Convergence.Conditions

--------------------------------------------------------------------------
-- We now construct a counterexample that obeys the above conditions but
-- does not converge to a unique fixed point
--------------------------------------------------------------------------
-- The underlying set is simply the set {0# , 1#}

--     -------------
--  1  | ↓ | ← | ↓ |
--     -------------
--  0  | ↺ | ← | ← |
--     -------------
--       0   1   2

pattern 0# = zero
pattern 1# = suc 0#
pattern 2# = suc 1#
pattern ## = suc (suc ())
pattern ### = suc (suc (suc ()))

--------------------------------------------------------------------------
-- The computation in question involves two node

Sᵢ : Fin 2 → Set _
Sᵢ 0# = Fin 3
Sᵢ 1# = Fin 2
Sᵢ ##

S : Set
S = ∀ i → Sᵢ i

[00] : S
[00] 0# = 0#
[00] 1# = 0#
[00] ##

[01] : S
[01] 0# = 0#
[01] 1# = 1#
[01] ##

[10] : S
[10] 0# = 1#
[10] 1# = 0#
[10] ##

[11] : S
[11] 0# = 1#
[11] 1# = 1#
[11] ##

[20] : S
[20] 0# = 2#
[20] 1# = 0#
[20] ##

[21] : S
[21] 0# = 2#
[21] 1# = 1#
[21] ##

--------------------------------------------------------------------------
-- Equality is clearly decidable

_≟ᵢ_ : Decidable Sᵢ _≡_
_≟ᵢ_ = {!!}

≡-isIndexedEquivalence : IsIndexedEquivalence Sᵢ _≡_
≡-isIndexedEquivalence = record
  { reflᵢ  = refl
  ; symᵢ   = sym
  ; transᵢ = trans
  }

≡-isIndexedDecEquivalence : IsIndexedDecEquivalence Sᵢ _≡_
≡-isIndexedDecEquivalence = record
  { _≟ᵢ_           = _≟ᵢ_
  ; isEquivalenceᵢ = ≡-isIndexedEquivalence
  }

--------------------------------------------------------------------------
-- The ordering will be the trivial total order (i.e. x ≤ y ⇔ x ≡ y)

_≤ᵢ_ : IRel Sᵢ 0ℓ
_≤ᵢ_ {0#} = _≤F_
_≤ᵢ_ {1#} = _≤F_
_≤ᵢ_ {##}

≤ᵢ-isIndexedPartialOrder : IsIndexedPartialOrder Sᵢ _≡_ _≤ᵢ_
≤ᵢ-isIndexedPartialOrder = record
  { isPreorderᵢ = record
    { isEquivalenceᵢ = ≡-isIndexedEquivalence
    ; reflexiveᵢ     = {!!}
    ; transᵢ         = {!!}
    }
  ; antisymᵢ         = {!!}
  }

_≤_ = Lift Sᵢ _≡_
_≈_ = Lift Sᵢ _≡_

--------------------------------------------------------------------------
-- The function being iterated is simply the identity function

F : S → S
F x with x 0# | x 1#
... | 0#  | 0# = [00]
... | 0#  | 1# = [00]
... | 1#  | 0# = [00]
... | 1#  | 1# = [01]
... | 2#  | 0# = [10]
... | 2#  | 1# = [20]
... | ### | _ 
... | _   | ##

F-cong : ∀ {x y} → x ≈ y → F x ≈ F y
F-cong x≈y = {!!}

F-isAsyncIterable : IsAsyncIterable _≡_ F
F-isAsyncIterable = record
  { isDecEquivalenceᵢ = ≡-isIndexedDecEquivalence
  ; F-cong            = F-cong
  }

F∥ : AsyncIterable 0ℓ 0ℓ 2
F∥ = record
  { isAsyncIterable = F-isAsyncIterable
  }

σ : ℕ → S → S
σ k = (F ^ k)

--------------------------------------------------------------------------
-- The setup above fulfils all the required properties

F-monotone : ∀ {x y} →  x ≤ y → F x ≤ F y
F-monotone = ?

F-decreasing : ∀ x → F x ≤ x
F-decreasing x with x 0# | x 1#
... | 0#  | 0# = {!!}
... | 0#  | 1# = {!!}
... | 1#  | 0# = {!!}
... | 1#  | 1# = {!!}
... | 2#  | 0# = {!!}
... | 2#  | 1# = {!!}
... | ### | _ 
... | _   | ##

σ-convergesTo-[00] : ∀ x → σ 3 x ≈ [00]
σ-convergesTo-[00] x i with x 0# | x 1#
... | 0#  | 0# = refl
... | 0#  | 1# = refl
... | 1#  | 0# = refl
... | 1#  | 1# = refl
... | 2#  | 0# = refl
... | 2#  | 1# = refl
... | ### | _ 
... | _   | ##

syncConditions : SynchronousConditions F∥ _
syncConditions = record
  { _≤ᵢ_              = _≤ᵢ_
  ; ≤ᵢ-isPartialOrder = ≤ᵢ-isIndexedPartialOrder
  ; F-monotone        = {!!}
  ; F-decreasing      = {!!}
  ; x*                = [00]
  ; x*-fixed          = λ i → refl
  ; k*                = 3
  ; σ-convergesTo-x*  = σ-convergesTo-[00]
  }

{-
--------------------------------------------------------------------------
-- Yet it converges to different non-equal fixed points depending on which
-- it starts in.

a-convergesTo-a : F 0#ₛ ≡ 0#ₛ
a-convergesTo-a = refl

b-convergesTo-b : F 1#ₛ ≡ 1#ₛ
b-convergesTo-b = refl
-}
