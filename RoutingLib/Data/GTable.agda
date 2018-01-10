open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Level using () renaming (suc to lsuc)
open import Relation.Unary using (Pred; _∈_)

open import RoutingLib.Data.Table using (Table)

module RoutingLib.Data.GTable where

  GTable : ∀ {a} n → Table {!Table ? ?!} n → Set a
  GTable n A = ∀ i → A i 

  GPred : ∀ {a n} {A : Table (Set a) n} → GTable n A → Set (lsuc a)
  GPred {a} {n} {A} t = ∀ i → Pred (A i) a --GTable n (λ i → Pred (A i) a)

  _∈ₜ_ : ∀ {a n} {A : Table (Set a) n} → GTable n A → GPred A → Set _
  t ∈ₜ P = ∀ i → {!t i!} ∈ P i
  
  -- Operations
{-  
  map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → ∀{n} → GTable A n → GTable B n
  map f t i = f (t i)

  zipWith : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} {n} →
            (A → B → C) → GTable A n → GTable B n → GTable C n
  zipWith f t s i = f (t i) (s i)

  zip : ∀ {a b} {A : Set a} {B : Set b} {n} →
        GTable A n → GTable B n → GTable (A × B) n
  zip = zipWith _,_

  
  foldl : ∀ {a b} {A : Set a} {B : Set b} →
          (B → A → B) → B → ∀ {n} → GTable A n → B
  foldl f e {zero}  t = e
  foldl f e {suc n} t = foldl f (f e (t fzero)) (t ∘ fsuc)
  
  foldr : ∀ {a b} {A : Set a} {B : Set b} →
          (A → B → B) → B → ∀ {n} → GTable A n → B
  foldr f e {zero}  t = e
  foldr f e {suc n} t = f (t fzero) (foldr f e (t ∘ fsuc))
  
  foldr⁺ : ∀ {a} {A : Set a} → Op₂ A → ∀ {n} → GTable A (suc n) → A
  foldr⁺ f {zero}  t = t fzero
  foldr⁺ f {suc n} t = f (t fzero) (foldr⁺ f (t ∘ fsuc))
  
  foldl⁺ : ∀ {a} {A : Set a} → Op₂ A → ∀ {n} → GTable A (suc n) → A
  foldl⁺ f {n} t = foldl f (t fzero) (t ∘ fsuc)

  max : ∀ {n} → ℕ → GTable ℕ n → ℕ
  max ⊥ t = foldr _⊔_ ⊥ t
  
  max⁺ : ∀ {n} → GTable ℕ (suc n) → ℕ
  max⁺ t = foldr⁺ _⊔_ t

  min : ∀ {n} → ℕ → GTable ℕ n → ℕ
  min ⊤ t = foldr _⊓_ ⊤ t
  
  min⁺ : ∀ {n} → GTable ℕ (suc n) → ℕ
  min⁺ t = foldr⁺ _⊓_ t
-}

