

module RoutingLib.Data.Integer.Properties where

open import Data.Nat as ℕ using (zero; suc; z≤n; s≤s)
import Data.Nat.Properties as ℕₚ
open import Data.Integer hiding (suc)
open import Data.Integer.Properties
open import Function using (_∘_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation using (contradiction)
open import RoutingLib.Function.Reasoning
import RoutingLib.Data.Nat.Properties as ℕₚ

_<?_ : Decidable _<_
i <? j = + 1 + i ≤? j

-[1+i]≡0⊖1+i : ∀ i → -[1+ i ] ≡ 0 ⊖ (suc i)
-[1+i]≡0⊖1+i i = refl

m⊖n≤m : ∀ m n → m ⊖ n ≤ + m
m⊖n≤m m       zero  = +≤+ ℕₚ.≤-refl
m⊖n≤m zero  (suc n) = -≤+
m⊖n≤m (suc m) (suc n) = ≤-trans (m⊖n≤m m n) (+≤+ (ℕₚ.n≤1+n m))

⊖-cancelʳ-≤ : ∀ m n o → m ⊖ n ≤ m ⊖ o → o ℕ.≤ n 
⊖-cancelʳ-≤ m        n       zero   _         = z≤n
⊖-cancelʳ-≤ (suc m) zero    (suc o) leq       = contradiction (≤-trans leq (m⊖n≤m m o)) (ℕₚ.n≮n m ∘ drop‿+≤+)
⊖-cancelʳ-≤ zero    (suc n) (suc o) (-≤- o≤n) = s≤s o≤n
⊖-cancelʳ-≤ (suc m) (suc n) (suc o) leq       = s≤s (⊖-cancelʳ-≤ m n o leq)

⊖-monoʳ-≤ : ∀ m {n o} → o ℕ.≤ n → m ⊖ n ≤ m ⊖ o 
⊖-monoʳ-≤ m       {n} z≤n       = m⊖n≤m m n
⊖-monoʳ-≤ zero    {_} (s≤s leq) = -≤- leq
⊖-monoʳ-≤ (suc m) {_} (s≤s leq) = ⊖-monoʳ-≤ m leq

-- *-monoʳ-≤-pos

*-monoʳ-<-non-neg : ∀ n → (_* + n) Preserves _<_ ⟶ _<_
*-monoʳ-<-non-neg (suc n)      i<j = {!!} --*-monoʳ-<-pos n
*-monoʳ-<-non-neg zero {i} {j} i<j = {!!}

*-monoˡ-<-non-neg : ∀ n → (+ n *_) Preserves _<_ ⟶ _<_
*-monoˡ-<-non-neg n {i} {j} i<j
  rewrite *-comm (+ n) i
        | *-comm (+ n) j
        = *-monoʳ-<-non-neg n i<j

*-monoˡ-<-pos : ∀ n → (+ suc n *_) Preserves _<_ ⟶ _<_
*-monoˡ-<-pos n = *-monoˡ-<-non-neg (suc n)

*-cancelʳ-<-pos : ∀ m n o → m * + suc o < n * + suc o → m < n
*-cancelʳ-<-pos (-[1+ m ]) (-[1+ n ]) o leq = begin⟨ leq ⟩
  ∴ 0 ⊖ (o ℕ.+ m ℕ.* suc o) ≤ 0 ⊖ (suc o ℕ.+ n ℕ.* suc o) $⟨ ⊖-cancelʳ-≤ 0 _ _ ⟩
  ∴ o ℕ.+ n ℕ.* suc o     ℕ.< o ℕ.+ m ℕ.* suc o           $⟨ ℕₚ.+-cancelˡ-< o ⟩
  ∴ n ℕ.* suc o           ℕ.< m ℕ.* suc o                 $⟨ ℕₚ.*-cancelʳ-< n m ⟩
  ∴ n                     ℕ.< m                           $⟨ ⊖-monoʳ-≤ 0 ⟩
  ∴ 0 ⊖ m                   ≤ 0 ⊖ suc n                   ∎
*-cancelʳ-<-pos -[1+ m ]   (+ _)      _ _         = -<+ {m}
*-cancelʳ-<-pos (+ 0)      (+ suc _)  _ _         = +≤+ (s≤s z≤n)
*-cancelʳ-<-pos (+ 0)      (+ 0)      _ (+≤+ ())
*-cancelʳ-<-pos (+ suc _)  (+ 0)      _ (+≤+ ())
*-cancelʳ-<-pos (+ suc m)  (+ suc n)  o (+≤+ m≤n) = +≤+ (ℕₚ.*-cancelʳ-< (suc m) (suc n) m≤n)

*-cancelˡ-<-pos : ∀ m n o → + suc m * n < + suc m * o → n < o
*-cancelˡ-<-pos m n o
  rewrite *-comm (+ suc m) n
        | *-comm (+ suc m) o
        = *-cancelʳ-<-pos n o m

