module RoutingLib.lmv34.EqualityProofs where

-- This file implements the exercises from the tutorial https://people.inf.elte.hu/divip/AgdaTutorial/Functions.Equality_Proofs.html#automatic-reduction-of-types

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit using (⊤; tt)

-- ≡ : Definition and properties
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

≡-refl : ∀ {A} (a : A) → a ≡ a
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
