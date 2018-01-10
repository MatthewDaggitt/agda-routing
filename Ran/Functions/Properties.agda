-- imports
open import Functions
open import Data.Nat
  using (ℕ; zero; suc; _≤_; _<_; _+_; _⊔_; _⊓_; z≤n; _*_)
open import Data.Fin
  using (Fin; toℕ; inject≤) renaming (zero to fzero; suc to fsuc)
open import Data.Product
  using (proj₁; ∃; _,_)
open import NatInf
  using (ℕ∞) renaming (_≤_ to _≤∞_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; subst; refl)
open import Level
  using () renaming (zero to lzero)
open import Relation.Unary
  using (Pred)
open import Algebra.FunctionProperties
  using (Op₂)
open import Function
  using (_∘_)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
open import Data.Nat.Properties
  using (m⊓n≤m; ≤-antisym; ⊔-sel)

module Functions.Properties where

  -- Properties of foldr
  _Forces-×ʳ_ : ∀ {a}{A : Set a} → Op₂ A → ∀ {p} → Pred A p → Set _
  _•_ Forces-×ʳ P = ∀ a b → P (a • b) → P b

  _⊎-Preservesʳ_ : ∀ {a}{A : Set a} → Op₂ A → ∀ {p} → Pred A p → Set _
  _•_ ⊎-Preservesʳ P = ∀ a {b} → P b → P (a • b)

  _⊎-Preserves_ : ∀ {a}{A : Set a} → Op₂ A → ∀ {p} → Pred A p → Set _
  _•_ ⊎-Preserves P = ∀ a b → P a ⊎ P b → P (a • b)
  
  _×-Preserves_ : ∀ {a}{A : Set a} → Op₂ A → ∀ {p} → Pred A p → Set _
  _•_ ×-Preserves P = ∀ {a b} → P a → P b → P (a • b)

  foldr-forces×ʳ : ∀ {P : Pred ℕ lzero}{_•_ : Op₂ ℕ} → 
                  _•_ Forces-×ʳ P → ∀ e {n} (t : Fin n → ℕ) →
                  P (foldr _•_ e t) → P e
  foldr-forces×ʳ forces _ {zero}  t Pe = Pe
  foldr-forces×ʳ forces e {suc n} t Pf =
      foldr-forces×ʳ forces e (t ∘ fsuc) (forces _ _ Pf)

  foldr-×pres : ∀ {P : Pred ℕ lzero}{_•_ : Op₂ ℕ} → _•_ ×-Preserves P → ∀ {e} → P e →
                  ∀ {n} {t : Fin n → ℕ} → (∀ i → P (t i)) →
                  P (foldr _•_ e t)
  foldr-×pres pres Pe {zero}  PM = Pe
  foldr-×pres {P} {op} pres Pe {suc n} PM = pres (PM fzero) (foldr-×pres {P} {op} pres Pe (PM ∘ fsuc))

  foldr-⊎presʳ : ∀ {P : Pred ℕ lzero}{_•_ : Op₂ ℕ} → _•_ ⊎-Preservesʳ P → ∀ {e} → P e →
                      ∀ {n} (t : Fin n → ℕ) → P (foldr _•_ e t)
  foldr-⊎presʳ pres Pe {zero}  t = Pe
  foldr-⊎presʳ pres Pe {suc n} t =
    pres _ (foldr-⊎presʳ pres Pe (t ∘ fsuc))
    
  foldr-⊎pres : ∀ {P : Pred ℕ lzero}{_•_ : Op₂ ℕ} → _•_ ⊎-Preserves P → ∀ e {n} {t : Fin n → ℕ} →
                     (∃ λ i → P (t i)) → P (foldr _•_ e t)
  foldr-⊎pres pres e (fzero  , Pt₀) = pres _ _ (inj₁ Pt₀)
  foldr-⊎pres pres e (fsuc i , Ptᵢ) =
    pres _ _ (inj₂ (foldr-⊎pres pres e (i , Ptᵢ)))

  

  -- properties of max and min
  postulate max-inc   : ∀ {n} f i → f i ≤ max {n} f
  postulate max-inc=n : ∀ {n} f → (∀ (i : Fin (suc n)) → (toℕ i) ≤ f i) → n ≤ max f
  postulate max-mono   : ∀ {n f g} → (∀ i → f i ≤ g i) → max {n} f ≤ max {n} g
  postulate max<      : ∀ {n f x} → (∀ (i : Fin n) → x < f i) → x < max f
  postulate max≤      : ∀ {n f x} → (∀ (i : Fin n) → x ≤ f i) → x ≤ max f
  postulate m≤n⇒maxₘ≤maxₙ  : ∀ {m n}{f : Fin m → ℕ}{g : Fin n → ℕ}(m≤n : m ≤ n) →
                        (∀ i → f i ≤ g (inject≤ i m≤n)) → max f ≤ max g
  postulate min∞-monotone : ∀ {n f g} → (∀ i → f i ≤∞ g i) → min∞ {n} f ≤∞ min∞ {n} g
  postulate min∞-dec : ∀ {n} f i → min∞ {n} f ≤∞ f i
  postulate min∞-equiv : ∀ {n g h} → (∀ i → g i ≡ h i) → min∞ {n} g ≡ min∞ {n} h


  -- properties of sum
  postulate sum-inc : ∀ {n f g} → (∀ i → f i ≤ g i) → sum {n} f ≤ sum {n} g
  postulate sum-inc-strict : ∀ {n f g} → (∀ i → f i ≤ g i) → ∃ (λ i → f i < g i)
                             → sum {n} f < sum {n} g
  postulate sum-limit : ∀ {n f x} → (∀ i → f i ≤ x) → sum {n} f ≤ x * n
  postulate x≤sum : ∀ {n i} f → f i ≤ sum {n} f
  postulate x+y≤sum² : ∀ {n} i j k (f : Fin n → Fin n → ℕ∞) (g : ℕ∞ → ℕ) →
                       g (f i k) + g (f k j) ≤ sum {n} (λ i₁ → sum {n} (λ j₁ → g (f i j)))
