module RoutingLib.Data.Table where

open import Data.Nat using (ℕ; zero; suc; _⊔_; _⊓_; _+_; _≟_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Fin using (Fin; toℕ; fromℕ; inject₁; lower₁; compare; equal; zero; suc; fromℕ≤)
open import Relation.Binary using (Rel; REL)
open import Relation.Unary using (Pred)
open import Relation.Nullary using (yes; no)
open import Data.Product using (∃; _×_; _,_)
open import Data.List as List using (List)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Fin.Subset using (Subset; ∣_∣; inside; outside; _∉_)
open import Level using (Level)
open import Function using (_∘_)
open import Algebra.FunctionProperties using (Op₂)

open import RoutingLib.Data.NatInf using (ℕ∞) renaming (_⊓_ to _⊓∞_)

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

Table : Set a → ℕ → Set a
Table A n = Fin n → A

-- Conversion

toList : ∀ {n} → Table A n → List A
toList = List.tabulate

toVec : ∀ {n} → Table A n → Vec A n
toVec = Vec.tabulate

-- Operations

map : (A → B) → ∀{n} → Table A n → Table B n
map f t i = f (t i)

zipWith : ∀ {n} → (A → B → C) → Table A n → Table B n → Table C n
zipWith f t s i = f (t i) (s i)

zip : ∀ {n} → Table A n → Table B n → Table (A × B) n
zip = zipWith _,_


foldl : (B → A → B) → B → ∀ {n} → Table A n → B
foldl f e {zero}  t = e
foldl f e {suc n} t = foldl f (f e (t zero)) (t ∘ suc)

foldr : (A → B → B) → B → ∀ {n} → Table A n → B
foldr f e {zero}  t = e
foldr f e {suc n} t = f (t zero) (foldr f e (t ∘ suc))

foldr⁺ : Op₂ A → ∀ {n} → Table A (suc n) → A
foldr⁺ f {zero}  t = t zero
foldr⁺ f {suc n} t = f (t zero) (foldr⁺ f (t ∘ suc))

foldl⁺ : Op₂ A → ∀ {n} → Table A (suc n) → A
foldl⁺ f {n} t = foldl f (t zero) (t ∘ suc)

max : ∀ {n} → ℕ → Table ℕ n → ℕ
max ⊥ t = foldr _⊔_ ⊥ t

max⁺ : ∀ {n} → Table ℕ (suc n) → ℕ
max⁺ t = foldr⁺ _⊔_ t

min : ∀ {n} → ℕ → Table ℕ n → ℕ
min ⊤ t = foldr _⊓_ ⊤ t

min⁺ : ∀ {n} → Table ℕ (suc n) → ℕ
min⁺ t = foldr⁺ _⊓_ t

min∞ : ∀ {n} → ℕ∞ → Table ℕ∞ n → ℕ∞
min∞ ⊤ t = foldr _⊓∞_ ⊤ t

min∞⁺ : ∀ {n} → Table ℕ∞ (suc n) → ℕ∞
min∞⁺ t = foldr⁺ _⊓∞_ t

sum : ∀ {n} → Table ℕ n → ℕ
sum t = foldr _+_ 0 t

⟦_⟧ : A → Table A 1
⟦ x ⟧ zero = x

[_]+_ : ∀ {n} → A → Table A n → Table A (suc n)
([ x ]+ t) zero    = x
([ x ]+ t) (suc i) = t i

_+[_] : ∀ {n} → Table A n → A → Table A (suc n)
_+[_] {n = n} t x i with n ≟ toℕ i
... | yes _   = x
... | no  n≢i = t (lower₁ i n≢i)

module _ {a} {A : Set a} where

  strip : ∀ {n} (p : Subset n) → Table A n → Table A ∣ p ∣
  strip []            f ()
  strip (outside ∷ p) f i       = strip p (f ∘ suc) i
  strip (inside  ∷ p) f zero    = f zero
  strip (inside  ∷ p) f (suc i) = strip p (f ∘ suc) i

  grow : ∀ {n} (p : Subset n) → Table A n → Table A ∣ p ∣ → Table A n
  grow []            t f ()
  grow (outside ∷ p) t f zero    = t zero
  grow (outside ∷ p) t f (suc i) = grow p (t ∘ suc) f i
  grow (inside  ∷ p) t f zero    = f zero
  grow (inside  ∷ p) t f (suc i) = grow p (t ∘ suc) (f ∘ suc) i
