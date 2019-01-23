open import Data.Nat using (ℕ; _≤_; zero; suc; s≤s)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (∃₂; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Function using (const; _$_)
open import Level using (0ℓ)
open import Relation.Binary using (_Respects_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≗_; refl)
open import Relation.Binary.Indexed.Homogeneous
open import Relation.Unary using (U; _∈_)

open import RoutingLib.Relation.Unary.Indexed

open import RoutingLib.Iteration.Asynchronous.Static
open import RoutingLib.Iteration.Asynchronous.Static.Convergence.Conditions

module RoutingLib.Iteration.Asynchronous.Static.Examples.NonNested where

pattern #0 = zero
pattern #1 = suc zero
pattern ## = suc (suc ())

Sᵢ : Fin 2 → Set
Sᵢ _ = Fin 2

S : Set
S = ∀ i → Sᵢ i


------------------------------------------------------------------------
--  Example operator
--    _____ _____
--   |     |     |
-- 1 |  ↓  |  ↻  |
--   |_____|_____|
--   |     |     |
-- 0 |  ↻  |  ↖  |
--   |_____|_____|
--      0     1

F : S → S
F x i with x #0 | x #1 | i
... | #0 | #0 | #0 = #0
... | #0 | #0 | #1 = #0
... | #0 | #1 | #0 = #0
... | #0 | #1 | #1 = #0
... | #1 | #0 | #0 = #0
... | #1 | #0 | #1 = #1
... | #1 | #1 | #0 = #0
... | #1 | #1 | #1 = #0
... | ## | _  | _
... | _  | ## | _
... | _  | _  | ##


F-isAsyncIterable : IsAsyncIterable _≡_ F
F-isAsyncIterable = record
  { isDecEquivalenceᵢ = {!!}
  ; F-cong           = {!!}
  }

𝓘 : AsyncIterable 0ℓ 0ℓ 2
𝓘 = record
  { Sᵢ              = Sᵢ
  ; _≈ᵢ_            = _≡_
  ; F               = F
  ; isAsyncIterable = F-isAsyncIterable
  }

------------------------------------------------------------------------
-- ACO conditions

B : ℕ → IPred Sᵢ 0ℓ
B 0 #0 = U
B 0 #1 = _≡ #0
B 1 #0 = _≡ #0
B 1 #1 = U
B _ i  = _≡ #0

Bᵢ-cong : ∀ {k i x y} → x ≡ y → x ∈ B k i → y ∈ B k i
Bᵢ-cong refl x∈Bₖ = x∈Bₖ

B₃-finish : ∀ {k} → 3 ≤ k → (const #0 ∈ᵢ B k × (∀ {x} → x ∈ᵢ B k → x ≗ const #0))
B₃-finish (s≤s (s≤s (s≤s _))) = const refl , _$_

B-finish : ∃₂ λ k* x* → ∀ {k} → k* ≤ k → (x* ∈ᵢ B k × (∀ {x} → x ∈ᵢ B k → x ≗ x*))
B-finish = 3 , const #0 , B₃-finish

F-resp-B₀ : ∀ {x} → x ∈ᵢ B 0 → F x ∈ᵢ B 0
F-resp-B₀ {x} x∈B₀ i with x #0 | x #1 | i
... | #0 | #0 | #0 = tt
... | #0 | #0 | #1 = refl
... | #0 | #1 | #0 = tt
... | #0 | #1 | #1 = refl
... | #1 | #0 | #0 = tt
... | #1 | #0 | #1 = {!!}
... | #1 | #1 | #0 = tt
... | #1 | #1 | #1 = refl
... | ## | _  | _
... | _  | ## | _
... | _  | _  | ##

F-mono-B   : ∀ {k x} → x ∈ᵢ B k → F x ∈ᵢ B (suc k)
F-mono-B {k} {x} x∈Bₖ i with x #0 | x #1 | i | k
... | #0 | #0 | #0 | 0     = refl
... | #0 | #0 | #0 | suc v = refl
... | #0 | #0 | #1 | 0     = tt
... | #0 | #0 | #1 | suc v = refl
... | #0 | #1 | #0 | 0     = refl
... | #0 | #1 | #0 | suc v = refl
... | #0 | #1 | #1 | 0     = tt
... | #0 | #1 | #1 | suc v = refl
... | #1 | #0 | #0 | 0     = refl
... | #1 | #0 | #0 | suc v = refl
... | #1 | #0 | #1 | 0     = tt
... | #1 | #0 | #1 | suc v = {!!}
... | #1 | #1 | #0 | 0     = refl
... | #1 | #1 | #0 | suc v = refl
... | #1 | #1 | #1 | 0     = tt
... | #1 | #1 | #1 | suc v = refl
... | ## | _  | _  | _
... | _  | ## | _  | _
... | _  | _  | ## | _

aco : ACO 𝓘 0ℓ
aco = record
  { B         = B
  ; Bᵢ-cong   = λ {k} {i} → Bᵢ-cong {k} {i}
  ; B-finish  = B-finish
  ; F-resp-B₀ = λ {x} → F-resp-B₀ {x}
  ; F-mono-B  = λ {k} {x} → F-mono-B {k} {x}
  }
