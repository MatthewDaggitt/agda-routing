module RoutingLib.lmv34.Playground.EqualityProofs where

-- This file implements the exercises from the tutorial https://people.inf.elte.hu/divip/AgdaTutorial/Functions.Equality_Proofs.html#automatic-reduction-of-types

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit using (⊤; tt)

-- ≡ : Definition and properties
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

≡-refl : forall {A} (a : A) → a ≡ a
≡-refl a = refl

≡-sym : ∀ {A} {a b : A} → a ≡ b → b ≡ a
≡-sym refl = refl

≡-trans : ∀ {A} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
≡-trans refl refl = refl

≡-cong : ∀ {A B} {m n : A} → (f : A → B) → m ≡ n → f m ≡ f n
≡-cong f refl = refl

-- + : Properties

+-right-identity : ∀ n → n + 0 ≡ n
+-right-identity zero = refl
+-right-identity (suc n) = ≡-cong suc (+-right-identity n)

+-left-identity : ∀ n → 0 + n ≡ n
+-left-identity n = refl

+-associative : ∀ a b c → a + (b + c) ≡ (a + b) + c
+-associative zero b c = refl
+-associative (suc a) b c = ≡-cong suc (+-associative a b c)

m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
m+1+n≡1+m+n zero n = refl
m+1+n≡1+m+n (suc m) n = ≡-cong suc (m+1+n≡1+m+n m n)

+-commutative : ∀ m n → m + n ≡ n + m
+-commutative zero n = ≡-sym (+-right-identity n)
+-commutative (suc m) n = ≡-trans
                        (≡-cong suc (+-commutative m n))
                        (≡-sym (m+1+n≡1+m+n n m))

-- List : Properties
fromList : List ⊤ → ℕ
fromList [] = zero
fromList (x ∷ xs) = suc (fromList xs)

toList : ℕ → List ⊤
toList zero = []
toList (suc n) = tt ∷ toList n

from-to : ∀ n → fromList (toList n) ≡ n
from-to zero = refl
from-to (suc n) = ≡-cong suc (from-to n)

to-from : ∀ xs → toList (fromList xs) ≡ xs
to-from [] = refl
to-from (x ∷ xs) = ≡-cong (λ ls → x ∷ ls) (to-from xs)

fromPreserves++ : ∀ (xs ys : List ⊤) → fromList (xs ++ ys) ≡ fromList xs + fromList ys
fromPreserves++ [] ys = refl
fromPreserves++ (x ∷ xs) ys = ≡-cong suc (fromPreserves++ xs ys)

toPreserves+ : ∀ (m n : ℕ) → toList (m + n) ≡ toList m ++ toList n
toPreserves+ zero n = refl
toPreserves+ (suc m) n = ≡-cong (λ ls → tt ∷ ls) (toPreserves+ m n)

-- Equational reasoning : Definition
_≡⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ refl ⟩ refl = refl

infixr 2 _≡⟨_⟩_

_▪ : ∀ {A : Set} (x : A) → x ≡ x
x ▪ = refl

infix 3 _▪

+-commutative' : (m n : ℕ) → m + n ≡ n + m
+-commutative' zero n = ≡-sym (+-right-identity n)
+-commutative' (suc m) n =
      suc m + n
    ≡⟨ refl ⟩
      suc (m + n)
    ≡⟨ ≡-cong suc (+-commutative' m n) ⟩
      suc (n + m)
    ≡⟨ ≡-sym (m+1+n≡1+m+n n m) ⟩
      n + suc m
    ▪

distribʳ-*-+ : ∀ a b c → (a + b) * c ≡ a * c + b * c
distribʳ-*-+ zero b c = refl
distribʳ-*-+ (suc a) b c =
       c + (a + b) * c
     ≡⟨ ≡-cong (λ x → c + x) (distribʳ-*-+ a b c) ⟩
       c + (a * c + b * c)
     ≡⟨ +-associative c (a * c) (b * c) ⟩
       c + a * c + b * c
     ▪

*-associative : ∀ a b c → a * (b * c) ≡ (a * b) * c
*-associative zero b c = refl
*-associative (suc a) b c =
       suc a * (b * c)
     ≡⟨ refl ⟩
       b * c + a * (b * c)
     ≡⟨ ≡-cong (λ h → b * c + h) (*-associative a b c) ⟩
       b * c + a * b * c
     ≡⟨ ≡-sym (distribʳ-*-+ b (a * b) c) ⟩
        (b + a * b) * c
     ≡⟨ refl ⟩
        (suc a * b) * c
     ▪

*-left-identity : ∀ a → 1 * a ≡ a
*-left-identity a = +-right-identity a

*-right-identity : ∀ a → a * 1 ≡ a
*-right-identity zero = refl
*-right-identity (suc a) = ≡-cong suc (*-right-identity a)

n*0≡0 : ∀ n → n * 0 ≡ 0
n*0≡0 zero = refl
n*0≡0 (suc n) = n*0≡0 n

+-suc : ∀ m n → suc (m + n) ≡ m + suc n
+-suc zero n = refl
+-suc (suc m) n = ≡-cong suc (+-suc m n)

*-suc : ∀ m n → m + m * n ≡ m * suc n
*-suc zero n = refl
*-suc (suc m) n =
      suc m + suc m * n
    ≡⟨ refl ⟩
      suc m + (n + m * n)
    ≡⟨ +-associative (suc m) n (m * n) ⟩
      suc m + n + m * n
    ≡⟨ ≡-cong (λ x → x + m * n) (+-suc m n) ⟩
      m + suc n + m * n
    ≡⟨ ≡-cong (λ x → x + m * n) (+-commutative m (suc n)) ⟩
      suc n + m + m * n
    ≡⟨ ≡-sym (+-associative (suc n) m (m * n)) ⟩
      suc n + (m + m * n)
    ≡⟨ ≡-cong (λ x → suc n + x) (*-suc m n) ⟩
      suc n + m * suc n
    ≡⟨ refl ⟩
      suc m * suc n
    ▪

*-comm : ∀ m n → m * n ≡ n * m
*-comm zero n = ≡-sym (n*0≡0 n)
*-comm (suc m) n =
       suc m * n
     ≡⟨ refl ⟩
       n + m * n
     ≡⟨ ≡-cong (λ x → n + x) (*-comm m n) ⟩
       n + n * m
     ≡⟨ *-suc n m ⟩
       n * suc m
     ▪

id : ∀ {A : Set} → A → A
id x = x

Σ : ℕ → (ℕ → ℕ) → ℕ
Σ zero f = zero
Σ (suc n) f = f (suc n) + Σ n f

infixr 10 Σ

x+x=2*x : ∀ n → n + n ≡ 2 * n
x+x=2*x n = ≡-cong (n +_) (≡-sym (+-right-identity n))

sumOfNats : ∀ n → 2 * Σ n id ≡ n * suc n
sumOfNats zero = refl
sumOfNats (suc n) =
      2 * (Σ (suc n) id)
    ≡⟨ refl ⟩
      2 * (suc n + Σ n id)
    ≡⟨ refl ⟩
      suc n + Σ n id + (suc n + Σ n id + 0)
    ≡⟨ ≡-cong (λ x → suc n + Σ n id + x) (+-right-identity (suc n + Σ n id)) ⟩
      suc n + Σ n id + (suc n + Σ n id)
    ≡⟨ +-associative ((suc n) + Σ n id) (suc n) (Σ n id) ⟩
      suc n + Σ n id + suc n + Σ n id
    ≡⟨ ≡-cong (_+ Σ n id) (+-commutative (suc n + Σ n id) (suc n))  ⟩
      suc n + (suc n + Σ n id) + Σ n id
    ≡⟨ ≡-cong (_+ Σ n id) (+-associative (suc n) (suc n) (Σ n id)) ⟩
      (suc n + suc n) + Σ n id + Σ n id
    ≡⟨ ≡-sym (+-associative (suc n + suc n) (Σ n id) (Σ n id)) ⟩
      suc n + suc n + (Σ n id + Σ n id)
    ≡⟨ ≡-cong (λ x → suc n + suc n + x) (x+x=2*x (Σ n id)) ⟩
      suc n + suc n + 2 * Σ n id
    ≡⟨ ≡-cong (suc n + suc n +_) (sumOfNats n) ⟩
      suc n + suc n + n * suc n
    ≡⟨ ≡-sym (+-associative (suc n) (suc n) (n * suc n)) ⟩
      suc n + (suc n + n * suc n)
    ≡⟨ refl ⟩
      suc (suc n) * suc n
    ≡⟨ *-comm (suc (suc n)) (suc n) ⟩
      suc n * suc (suc n) ▪
