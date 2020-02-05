

module RoutingLib.Data.Nat.Pairing where

open import Data.Nat using (ℕ; _*_; _+_; _∸_; _≤_; _<_)
open import Data.Nat.Properties
open import Data.Vec.Functional
open import Data.Product
open import Data.Product.Properties
open import Data.Product.Relation.Binary.Lex.NonStrict
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
open import Level using (Level)
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Binary

open import RoutingLib.Function.Metric
open import RoutingLib.Data.Fin.Properties
open import RoutingLib.Data.Vec.Functional.Relation.Binary.Lex as Lex using (Lex)

private
  variable
    a : Level
    A : Set a

  _≤ₗₑₓ_ : ∀ {n} → Rel (Vector ℕ n) _
  _≤ₗₑₓ_ = Lex ⊤ _≡_ _≤_


module _ (m n : ℕ) where

  pair : ℕ → ℕ → ℕ
  pair x y = x * n + y 

  pair-bounded : ∀ {x y} → x < m → y < n → pair x y < m * n
  pair-bounded {x} {y} x<m y<n = begin-strict
    x * n       + y ≤⟨ {!!} ⟩
    (m ∸ 1) * n + y <⟨ {!!} ⟩
    (m ∸ 1) * n + n ≡⟨ {!!} ⟩
    m * n ∸ m + n   ≡⟨ {!!} ⟩
    m * n           ∎
    where open ≤-Reasoning

  pair-injective₁ : ∀ {x y u v} → x < m → y < n → u < m → v < m → pair x y ≡ pair u v → u ≡ x
  pair-injective₁ = {!!}

  pair-injective₂ : ∀ {x y u v} → x < m → y < n → u < m → v < m → pair x y ≡ pair u v → v ≡ y
  pair-injective₂ = {!!}
  

module _ (m n : ℕ) where

  pairAll : Vector ℕ n → ℕ
  pairAll xs = foldr (pair m n) 0 xs

  pairAll[xs]≡0⇒xs≡0ᵛ : ∀ xs → pairAll xs ≡ 0 → xs ≡ replicate 0
  pairAll[xs]≡0⇒xs≡0ᵛ xs = {!!}

  xs≡0ᵛ⇒pairAll[xs]≡0 : ∀ xs → xs ≡ replicate 0 → pairAll xs ≡ 0
  xs≡0ᵛ⇒pairAll[xs]≡0 = {!!}

  pairAll-bounded : ∀ xs → pairAll xs < m * n
  pairAll-bounded xs = {!!}

  pairAll-mono : ∀ {xs ys} → xs ≤ₗₑₓ ys → pairAll xs ≤ pairAll ys
  pairAll-mono xs≤ys = {!!}

  pairAll-cancel : ∀ {xs ys} → pairAll xs ≤ pairAll ys → xs ≤ₗₑₓ ys
  pairAll-cancel p[xs]≤p[ys] = {!!}
  

module _ {n : ℕ} (dᵥ : Distance A (Vector ℕ n))
         {m : ℕ} (dᵥ-bounded : ∀ x y i → dᵥ x y i ≤ m)
         where

  private
    0ᵛ : Vector ℕ n
    0ᵛ = replicate 0

    
  d : Distance A ℕ
  d x y = pairAll m n (dᵥ x y)

  dxy≡0⇒x≈y : Indiscernable _≡_ _≡_ dᵥ 0ᵛ → Indiscernable _≡_ _≡_ d 0
  dxy≡0⇒x≈y ind dxy≡0 = ind (pairAll[xs]≡0⇒xs≡0ᵛ m n _ dxy≡0)

  x≈y⇒dxy≡0 : Definite _≡_ _≡_ dᵥ 0ᵛ → Definite _≡_ _≡_ d 0
  x≈y⇒dxy≡0 def x≈y = xs≡0ᵛ⇒pairAll[xs]≡0 m n _ (def x≈y)

  d-bounded : ∀ x y → d x y < m * n
  d-bounded x y = pairAll-bounded m n (dᵥ x y)

  d-mono-≤ : ∀ v x y → dᵥ x y ≤ₗₑₓ v → d x y ≤ pairAll m n v
  d-mono-≤ v x y dᵥ≤v = pairAll-mono m n dᵥ≤v 
