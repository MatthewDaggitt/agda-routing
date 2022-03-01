module RoutingLib.Data.Nat.DivMod where

open import Agda.Builtin.Nat using (div-helper; mod-helper)

open import Data.Fin using (Fin; zero; toℕ; fromℕ<)
open import Data.Fin.Properties
open import Data.Nat 
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Nat.DivMod.Core
open import Data.Nat.Divisibility
open import Relation.Binary.PropositionalEquality

open import RoutingLib.Data.Nat.DivMod.Core
open import RoutingLib.Data.Fin.Properties hiding (≤-pred)

open ≡-Reasoning

------------------------------------------------------------------------
-- _%_

-- stdlib v2.0 (m%n<n)
m%[1+n]≤n : ∀ m n → m % suc n ≤ n
m%[1+n]≤n m n = a[modₕ]n<n 0 m n

[m∸m%n]%n≡0 : ∀ m n → (m ∸ m % suc n) % suc n ≡ 0
[m∸m%n]%n≡0 m n = modₕ-minus 0 m n


-- Switch to _%_ in v2.0
%≡0⇒mod≡0 : ∀ m {n} → m % suc n ≡ zero → m mod suc n ≡ zero
%≡0⇒mod≡0 m eq = fromℕ<-cong _ _ eq (m%n<n m _) (s≤s z≤n)

n[mod]n≡0 : ∀ n → suc n mod suc n ≡ zero
n[mod]n≡0 n = fromℕ<-cong _ _ (n%n≡0 n) (m%n<n (suc n) n) (s≤s z≤n)

toℕ-mod : ∀ {n} (i : Fin (suc n)) → toℕ i mod suc n ≡ i
toℕ-mod {n} i = begin
  fromℕ< (m%n<n (toℕ i) n)  ≡⟨ fromℕ<-cong _ _ (m≤n⇒m%n≡m (≤-pred (toℕ<n i))) (m%n<n (toℕ i) n) (toℕ<n i) ⟩
  fromℕ< (toℕ<n i)          ≡⟨ fromℕ<-toℕ i (toℕ<n i) ⟩
  i                         ∎

+ˡ-mod : ∀ {a} b {n} → suc n ∣ a → (a + b) mod suc n ≡ b mod suc n
+ˡ-mod {a} b eq = fromℕ<-cong _ _ (%-remove-+ˡ b eq) (m%n<n (a + b) _) (m%n<n b _)

+ʳ-mod : ∀ a {b} {n} → suc n ∣ b → (a + b) mod suc n ≡ a mod suc n
+ʳ-mod a {b} eq = fromℕ<-cong _ _ (%-remove-+ʳ a eq) (m%n<n (a + b) _) (m%n<n a _)
