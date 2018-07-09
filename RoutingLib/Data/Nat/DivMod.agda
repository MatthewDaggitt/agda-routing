------------------------------------------------------------------------
-- Copied from the stdlib v0.17
------------------------------------------------------------------------

module RoutingLib.Data.Nat.DivMod where

open import Agda.Builtin.Nat using (div-helper; mod-helper)

open import Data.Fin using (Fin; zero; toℕ; fromℕ≤″; fromℕ≤)
open import Data.Fin.Properties using (toℕ<n)
open import Data.Nat as Nat
open import Data.Nat.Properties using (≤⇒≤″; +-assoc; +-comm; +-identityʳ)
open import Data.Nat.DivMod using (_mod_)
open import Relation.Nullary.Decidable using (False)
open import Relation.Binary.PropositionalEquality
import Relation.Binary.PropositionalEquality.TrustMe as TrustMe
  using (erase)

open import RoutingLib.Data.Nat.DivMod.Core
open import RoutingLib.Data.Fin.Properties

open ≡-Reasoning

------------------------------------------------------------------------
-- Basic operations

infixl 7 _div_ _%_

-- Integer division

_div_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → ℕ
(a div 0) {}
(a div suc n) = div-helper 0 n a n

-- Integer remainder (mod)

_%_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → ℕ
(a % 0) {}
(a % suc n) = mod-helper 0 n a n

------------------------------------------------------------------------
-- _div_

a≡a%n+[a/n]*n : ∀ a n → a ≡ a % suc n + (a div (suc n)) * suc n
a≡a%n+[a/n]*n a n = division-lemma 0 0 a n

------------------------------------------------------------------------
-- _%_

a%1≡0 : ∀ a → a % 1 ≡ 0
a%1≡0 = a[modₕ]1≡0

a%n<n : ∀ a n → a % (suc n) < (suc n)
a%n<n a n = s≤s (mod-lemma 0 a n)

a%n≤a : ∀ a n → a % (suc n) ≤ a
a%n≤a a n = a[modₕ]n≤a 0 a n

n%n≡0 : ∀ n → suc n % suc n ≡ 0
n%n≡0 n = n[modₕ]n≡0 0 n

a%n%n≡a%n : ∀ a n → a % suc n % suc n ≡ a % suc n
a%n%n≡a%n a n = modₕ-absorb 0 a n

[a+n]%n≡a%n : ∀ a n → (a + suc n) % suc n ≡ a % suc n
[a+n]%n≡a%n a n = a+n[modₕ]n≡a[modₕ]n 0 a n

[a+kn]%n≡a%n : ∀ a k n → (a + k * (suc n)) % suc n ≡ a % suc n
[a+kn]%n≡a%n a zero    n = cong (_% suc n) (+-identityʳ a)
[a+kn]%n≡a%n a (suc k) n = begin
  (a + (m + k * m)) % m ≡⟨ cong (_% m) (sym (+-assoc a m (k * m))) ⟩
  (a + m + k * m)   % m ≡⟨ [a+kn]%n≡a%n (a + m) k n ⟩
  (a + m)           % m ≡⟨ [a+n]%n≡a%n a n ⟩
  a                 % m ∎
  where m = suc n

kn%n≡0 : ∀ k n → k * (suc n) % (suc n) ≡ 0
kn%n≡0 = [a+kn]%n≡a%n 0

%-distribˡ-+ : ∀ a b n → (a + b) % suc n ≡ (a % suc n + b % suc n) % suc n
%-distribˡ-+ a b n = begin
  (a + b)                           % m ≡⟨ cong (λ v → (v + b) % m) (a≡a%n+[a/n]*n a n) ⟩
  (a % m + a div m * m + b)         % m ≡⟨ cong (_% m) (+-assoc (a % m) _ b) ⟩
  (a % m + (a div m * m + b))       % m ≡⟨ cong (λ v → (a % m + v) % m) (+-comm _ b) ⟩
  (a % m + (b + a div m * m))       % m ≡⟨ cong (_% m) (sym (+-assoc (a % m) b _)) ⟩
  (a % m + b + a div m * m)         % m ≡⟨ [a+kn]%n≡a%n (a % m + b) (a div m) n ⟩
  (a % m + b)                       % m ≡⟨ cong (λ v → (a % m + v) % m) (a≡a%n+[a/n]*n b n) ⟩
  (a % m + (b % m + (b div m) * m)) % m ≡⟨ sym (cong (_% m) (+-assoc (a % m) (b % m) _)) ⟩
  (a % m +  b % m + (b div m) * m)  % m ≡⟨ [a+kn]%n≡a%n (a % m + b % m) (b div m) n ⟩
  (a % m + b % m)                   % m ∎
  where m = suc n




-- Not in standard library


a%[1+n]≤n : ∀ a n → a % suc n ≤ n
a%[1+n]≤n a n = mod-lemma 0 a n

a≤n⇒a%n≡a : ∀ {a n} → a ≤ n → a % suc n ≡ a
a≤n⇒a%n≡a {a} {n} a≤n with ≤⇒≤″ a≤n
... | less-than-or-equal {k} refl = modₕ-skipToEnd 0 (a + k) a k

[a∸a%n]%n≡0 : ∀ a n → (a ∸ a % suc n) % suc n ≡ 0
[a∸a%n]%n≡0 a n = modₕ-minus 0 a n

+ˡ-% : ∀ a b {n} → a % suc n ≡ 0 → (a + b) % suc n ≡ b % suc n
+ˡ-% a b {n} eq = begin
  (a + b) % suc n                 ≡⟨ %-distribˡ-+ a b n ⟩
  (a % suc n + b % suc n) % suc n ≡⟨ cong (λ v → (v + b % suc n) % suc n) eq ⟩
  (b % suc n) % suc n             ≡⟨ a%n%n≡a%n b n ⟩
  b % suc n                       ∎

+ʳ-% : ∀ a b {n} → b % suc n ≡ 0 → (a + b) % suc n ≡ a % suc n
+ʳ-% a b {n} eq = trans (cong (_% suc n) (+-comm a b)) (+ˡ-% b a eq)





%⇒mod≡0 : ∀ a {n} → a % suc n ≡ zero → a mod suc n ≡ zero
%⇒mod≡0 a eq = fromℕ≤″-cong _ (≤⇒≤″ (s≤s z≤n)) eq

n[mod]n≡0 : ∀ n → suc n mod suc n ≡ zero
n[mod]n≡0 n = fromℕ≤″-cong _ (≤⇒≤″ (s≤s z≤n)) (n%n≡0 n)

toℕ-mod : ∀ {n} (i : Fin (suc n)) → toℕ i mod suc n ≡ i
toℕ-mod {n} i = begin
  fromℕ≤″ (toℕ i % suc n) _  ≡⟨ fromℕ≤″-cong _ _ (a≤n⇒a%n≡a (≤-pred (toℕ<n i))) ⟩
  fromℕ≤″ (toℕ i) _          ≡⟨ fromℕ≤″-toℕ (≤⇒≤″ (toℕ<n i)) ⟩
  i                           ∎
  
+ˡ-mod : ∀ a b {n} → a mod suc n ≡ zero → (a + b) mod suc n ≡ b mod suc n
+ˡ-mod a b eq = fromℕ≤″-cong _ _ (+ˡ-% a b (fromℕ≤″-injective _ (≤⇒≤″ (s≤s z≤n)) eq))

+ʳ-mod : ∀ a b {n} → b mod suc n ≡ zero → (a + b) mod suc n ≡ a mod suc n
+ʳ-mod a b eq = fromℕ≤″-cong _ _ (+ʳ-% a b (fromℕ≤″-injective _ (≤⇒≤″ (s≤s z≤n)) eq))