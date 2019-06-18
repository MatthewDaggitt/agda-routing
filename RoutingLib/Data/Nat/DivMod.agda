------------------------------------------------------------------------
-- Copied from the stdlib v0.17
------------------------------------------------------------------------

module RoutingLib.Data.Nat.DivMod where

open import Agda.Builtin.Nat using (div-helper; mod-helper)

open import Data.Fin using (Fin; zero; toℕ; fromℕ≤″; fromℕ≤)
open import Data.Fin.Properties using (toℕ<n; fromℕ≤-toℕ)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Nat.DivMod.Core
open import Data.Nat.Divisibility
open import Relation.Binary.PropositionalEquality

open import RoutingLib.Data.Nat.DivMod.Core
open import RoutingLib.Data.Fin.Properties

open ≡-Reasoning

------------------------------------------------------------------------
-- _%_


-- Check if needed
a%[1+n]≤n : ∀ a n → a % suc n ≤ n
a%[1+n]≤n a n = a[modₕ]n<n 0 a n

[a∸a%n]%n≡0 : ∀ a n → (a ∸ a % suc n) % suc n ≡ 0
[a∸a%n]%n≡0 a n = modₕ-minus 0 a n

%⇒mod≡0 : ∀ a {n} → a % suc n ≡ zero → a mod suc n ≡ zero
%⇒mod≡0 a eq = fromℕ≤-cong (a%n<n a _) (s≤s z≤n) eq

n[mod]n≡0 : ∀ n → suc n mod suc n ≡ zero
n[mod]n≡0 n = fromℕ≤-cong (a%n<n (suc n) n) (s≤s z≤n) (n%n≡0 n)

toℕ-mod : ∀ {n} (i : Fin (suc n)) → toℕ i mod suc n ≡ i
toℕ-mod {n} i = begin
  fromℕ≤ (a%n<n (toℕ i) n)  ≡⟨ fromℕ≤-cong (a%n<n (toℕ i) n) (toℕ<n i) (m≤n⇒m%n≡m (≤-pred (toℕ<n i))) ⟩
  fromℕ≤ (toℕ<n i)          ≡⟨ fromℕ≤-toℕ i (toℕ<n i) ⟩
  i                         ∎

+ˡ-mod : ∀ {a} b {n} → suc n ∣ a → (a + b) mod suc n ≡ b mod suc n
+ˡ-mod {a} b eq = fromℕ≤-cong (a%n<n (a + b) _) (a%n<n b _) (%-remove-+ˡ b eq)

+ʳ-mod : ∀ a {b} {n} → suc n ∣ b → (a + b) mod suc n ≡ a mod suc n
+ʳ-mod a {b} eq = fromℕ≤-cong (a%n<n (a + b) _) (a%n<n a _) (%-remove-+ʳ a eq)
