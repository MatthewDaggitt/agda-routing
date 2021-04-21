
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
open import Function.Base using (_∘_)
open import Algebra.Core using (Op₂)

open import RoutingLib.Data.NatInf using (ℕ∞) renaming (_⊓_ to _⊓∞_)

open import Data.Vec.Functional

module RoutingLib.Data.Vec.Functional where


private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

-- Operations

foldr⁺ : Op₂ A → ∀ {n} → Vector A (suc n) → A
foldr⁺ f {zero}  t = t zero
foldr⁺ f {suc n} t = f (t zero) (foldr⁺ f (t ∘ suc))

foldl⁺ : Op₂ A → ∀ {n} → Vector A (suc n) → A
foldl⁺ f {n} t = foldl f (t zero) (t ∘ suc)

max : ∀ {n} → ℕ → Vector ℕ n → ℕ
max ⊥ t = foldr _⊔_ ⊥ t

max⁺ : ∀ {n} → Vector ℕ (suc n) → ℕ
max⁺ t = foldr⁺ _⊔_ t

min : ∀ {n} → ℕ → Vector ℕ n → ℕ
min ⊤ t = foldr _⊓_ ⊤ t

min⁺ : ∀ {n} → Vector ℕ (suc n) → ℕ
min⁺ t = foldr⁺ _⊓_ t

min∞ : ∀ {n} → ℕ∞ → Vector ℕ∞ n → ℕ∞
min∞ ⊤ t = foldr _⊓∞_ ⊤ t

min∞⁺ : ∀ {n} → Vector ℕ∞ (suc n) → ℕ∞
min∞⁺ t = foldr⁺ _⊓∞_ t

sum : ∀ {n} → Vector ℕ n → ℕ
sum t = foldr _+_ 0 t

⟦_⟧ : A → Vector A 1
⟦ x ⟧ zero = x

_∷ʳ_ : ∀ {n} → Vector A n → A → Vector A (suc n)
_∷ʳ_ {n = n} t x i with n ≟ toℕ i
... | yes _   = x
... | no  n≢i = t (lower₁ i n≢i)
