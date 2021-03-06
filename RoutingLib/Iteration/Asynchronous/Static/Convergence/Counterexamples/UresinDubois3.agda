--------------------------------------------------------------------------
-- Agda routing library
--
-- A counter-example of proposition 3 by Uresin & Dubois
--------------------------------------------------------------------------

module RoutingLib.Iteration.Asynchronous.Static.Convergence.Counterexamples.UresinDubois3 where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product
open import Level using (0ℓ; _⊔_) renaming (suc to lsuc)
import Relation.Binary as B
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Indexed.Homogeneous
open import Relation.Unary using (U)
open import Relation.Unary.Properties using (U-Universal)

open import RoutingLib.Relation.Unary.Indexed

open import RoutingLib.Iteration.Synchronous
open import RoutingLib.Iteration.Asynchronous.Static

--------------------------------------------------------------------------
-- The synchronous conditions as described by U&D. The problem is that the
-- field "σ-converges" does not guarantee the fixed point converged to
-- will always be the same fixed point.

record SynchronousConditions {a ℓ n} (F∥ : AsyncIterable a ℓ n) p o
                             : Set (lsuc (a ⊔ ℓ ⊔ p ⊔ o)) where
  open AsyncIterable F∥

  private
    σ : ℕ → S → S
    σ k = (F ^ k)

  field
    B₀               : IPred Sᵢ p
    B₀-cong          : ∀ {x y} → x ∈ᵢ B₀ → x ≈ y → y ∈ᵢ B₀
    B₀-closed        : ∀ {x} → x ∈ᵢ B₀ → F x ∈ᵢ B₀

    _≤ᵢ_              : IRel Sᵢ o
    ≤ᵢ-isPartialOrder : IsIndexedPartialOrder Sᵢ _≈ᵢ_ _≤ᵢ_

  open IsIndexedPartialOrder ≤ᵢ-isPartialOrder public
  _≤_ = Lift Sᵢ _≤ᵢ_

  field
    F-monotone    : ∀ {x y} → x ∈ᵢ B₀ → y ∈ᵢ B₀ → x ≤ y → F x ≤ F y
    F-cong        : ∀ {x y} → x ≈ y → F x ≈ F y
    σ-decreasing  : ∀ {x} → x ∈ᵢ B₀ → ∀ k → σ (suc k) x ≤ σ k x
    σ-converges   : ∀ {x} → x ∈ᵢ B₀ → ∃ λ k* → ∀ k → σ k* x ≈ σ (k* + k) x


--------------------------------------------------------------------------
-- We now construct a counterexample that obeys the above conditions but
-- does not converge to a unique fixed point
--------------------------------------------------------------------------
-- The underlying set is simply the set {0# , 1#}

open import Data.Sign renaming (Sign to Bit; + to 0#; - to 1#)

--------------------------------------------------------------------------
-- The computation in question is only going to involve a single node

Sᵢ : Fin 1 → Set _
Sᵢ i = Bit

S : Set
S = ∀ i → Sᵢ i

--------------------------------------------------------------------------
-- Therefore there are only two possible states

0#ₛ : S 
0#ₛ _ = 0#

1#ₛ : S
1#ₛ _ = 1#

--------------------------------------------------------------------------
-- Equality is clearly decidable

≡-isIndexedEquivalence : IsIndexedEquivalence Sᵢ _≡_
≡-isIndexedEquivalence = record
  { reflᵢ  = refl
  ; symᵢ   = sym
  ; transᵢ = trans
  }

≡-isIndexedDecEquivalence : IsIndexedDecEquivalence Sᵢ _≡_
≡-isIndexedDecEquivalence = record
  { _≟ᵢ_           = _≟_
  ; isEquivalenceᵢ = ≡-isIndexedEquivalence
  }

--------------------------------------------------------------------------
-- The ordering will be the trivial total order (i.e. x ≤ y ⇔ x ≡ y)

≡-isIndexedPartialOrder : IsIndexedPartialOrder Sᵢ _≡_ _≡_
≡-isIndexedPartialOrder = record
  { isPreorderᵢ = record
    { isEquivalenceᵢ = ≡-isIndexedEquivalence
    ; reflexiveᵢ     = λ { refl → refl }
    ; transᵢ         = trans
    }
  ; antisymᵢ         = λ { refl _ → refl }
  }

_≤_ = Lift Sᵢ _≡_
_≈_ = Lift Sᵢ _≡_

--------------------------------------------------------------------------
-- The function being iterated is simply the identity function

F : S → S
F x = x

F-cong : ∀ {x y} → x ≈ y → F x ≈ F y
F-cong x≈y = x≈y

F-isAsyncIterable : IsAsyncIterable _≡_ F
F-isAsyncIterable = record
  { isDecEquivalenceᵢ = ≡-isIndexedDecEquivalence
  ; F-cong            = F-cong
  }

F∥ : AsyncIterable 0ℓ 0ℓ 1
F∥ = record
  { isAsyncIterable = F-isAsyncIterable
  }

σ : ℕ → S → S
σ k = (F ^ k)

--------------------------------------------------------------------------
-- The setup above fulfils all the required properties

B₀ : IPred Sᵢ _
B₀ i x = U x

_∈B₀ : S → Set _
x ∈B₀ = ∀ i → B₀ i (x i)

B₀-cong : ∀ {x y} → x ∈B₀ → x ≈ y → y ∈B₀
B₀-cong {_} {y} _ _ i = U-Universal (y i)

B₀-closed : ∀ {s} → s ∈B₀ → F s ∈B₀
B₀-closed {s} s∈B₀ i = U-Universal (s i)

F-monotone : ∀ {x y} → x ∈B₀ → y ∈B₀ → x ≤ y → F x ≤ F y
F-monotone _ _ x≼y i = x≼y i

σᵏ≗id : ∀ k x → x ≈ σ k x
σᵏ≗id zero    x i = refl
σᵏ≗id (suc k) x i = σᵏ≗id k x i

σ-decreasing : ∀ {x} → x ∈B₀ → ∀ k → σ (suc k) x ≤ σ k x
σ-decreasing _ k i = refl

σ-converges : ∀ {x} → x ∈B₀ → ∃ λ k* → ∀ k → σ k* x ≈ σ (k* + k) x
σ-converges {x} _ = 0 , λ k → σᵏ≗id k x

syncConditions : SynchronousConditions F∥ _ _
syncConditions = record
  { B₀                = B₀
  ; B₀-cong           = B₀-cong
  ; B₀-closed         = λ {s} → B₀-closed {s}
  ; _≤ᵢ_              = _≡_
  ; ≤ᵢ-isPartialOrder = ≡-isIndexedPartialOrder
  ; F-monotone        = F-monotone
  ; F-cong            = F-cong
  ; σ-decreasing      = σ-decreasing
  ; σ-converges       = σ-converges
  }

--------------------------------------------------------------------------
-- Yet it converges to different non-equal fixed points depending on which
-- it starts in.

a-convergesTo-a : F 0#ₛ ≡ 0#ₛ
a-convergesTo-a = refl

b-convergesTo-b : F 1#ₛ ≡ 1#ₛ
b-convergesTo-b = refl
