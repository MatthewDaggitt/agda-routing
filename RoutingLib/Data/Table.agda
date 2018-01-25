open import Data.Nat using (ℕ; zero; suc; _⊔_; _⊓_)
open import Data.Fin using (Fin; toℕ; fromℕ; inject₁; compare; equal) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary using (Rel; REL)
open import Relation.Unary using (Pred)
open import Data.Product using (∃; _×_; _,_)
open import Data.List as List using (List)
open import Data.Vec as Vec using (Vec)
open import Function using (_∘_)
open import Algebra.FunctionProperties using (Op₂)

open import RoutingLib.Data.NatInf using (ℕ∞) renaming (_⊓_ to _⊓∞_)

module RoutingLib.Data.Table where

  Table : ∀ {a} → Set a → ℕ → Set a
  Table A n = Fin n → A
  
  -- Conversion
  
  toList : ∀ {a n} {A : Set a} → Table A n → List A
  toList = List.tabulate

  toVec : ∀ {a n} {A : Set a} → Table A n → Vec A n
  toVec = Vec.tabulate

  -- Operations
  
  map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → ∀{n} → Table A n → Table B n
  map f t i = f (t i)

  zipWith : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} {n} →
            (A → B → C) → Table A n → Table B n → Table C n
  zipWith f t s i = f (t i) (s i)

  zip : ∀ {a b} {A : Set a} {B : Set b} {n} →
        Table A n → Table B n → Table (A × B) n
  zip = zipWith _,_

  
  foldl : ∀ {a b} {A : Set a} {B : Set b} →
          (B → A → B) → B → ∀ {n} → Table A n → B
  foldl f e {zero}  t = e
  foldl f e {suc n} t = foldl f (f e (t fzero)) (t ∘ fsuc)
  
  foldr : ∀ {a b} {A : Set a} {B : Set b} →
          (A → B → B) → B → ∀ {n} → Table A n → B
  foldr f e {zero}  t = e
  foldr f e {suc n} t = f (t fzero) (foldr f e (t ∘ fsuc))
  
  foldr⁺ : ∀ {a} {A : Set a} → Op₂ A → ∀ {n} → Table A (suc n) → A
  foldr⁺ f {zero}  t = t fzero
  foldr⁺ f {suc n} t = f (t fzero) (foldr⁺ f (t ∘ fsuc))
  
  foldl⁺ : ∀ {a} {A : Set a} → Op₂ A → ∀ {n} → Table A (suc n) → A
  foldl⁺ f {n} t = foldl f (t fzero) (t ∘ fsuc)

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

