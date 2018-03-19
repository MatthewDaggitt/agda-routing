open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _⊓_; _⊔_)
open import Data.Nat.Properties using (⊔-sel; ≤-refl; ≤-antisym; ≤-reflexive)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_,_; proj₂; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Binary using (Rel; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong₂)
open import Relation.Unary using (Pred)
open import Algebra.FunctionProperties using (Op₂; Selective)

open import RoutingLib.Data.Matrix
open import RoutingLib.Data.Matrix.Relation.Pointwise using (Pointwise; fold⁺-cong)
open import RoutingLib.Data.Matrix.Membership.Propositional using (_∈_)
open import RoutingLib.Data.Nat.Properties
open import RoutingLib.Data.Table as Table using (Table)
open import RoutingLib.Data.Table.All using () renaming (All to TableAll)
import RoutingLib.Data.Table.Properties as TableP
open import RoutingLib.Algebra.FunctionProperties

module RoutingLib.Data.Matrix.Properties where

  -- Properties fold

  module _ {a p} {A : Set a} (P : Pred A p) {_•_ : Op₂ A} where
  
    fold-×pres : _•_ Preservesᵇ P → ∀ {e : A} → P e →
                 ∀ {m n} {M : Matrix A m n} → All P M →
                 P (fold _•_ e M)
    fold-×pres pres Pe {zero}  PM = Pe
    fold-×pres pres Pe {suc m} PM = TableP.foldr-×pres P pres
      (fold-×pres pres Pe (PM ∘ fsuc)) (PM fzero)

    fold-⊎pres : _•_ Preservesᵒ P → ∀ e {m n} {M : Matrix A  m n} →
                 Any P M → P (fold _•_ e M)
    fold-⊎pres pres e {M}     (fzero , PMᵢ)  = TableP.foldr-⊎pres P pres _ PMᵢ
    fold-⊎pres pres e {M = M} (fsuc i , PMᵢ) = TableP.foldr-⊎presʳ P (presᵒ⇒presʳ pres)
      (fold-⊎pres pres e (i , PMᵢ)) (M fzero)

    fold-⊎presʳ : _•_ Preservesʳ P → ∀ {e} → P e →
                 ∀ {m n} (M : Matrix A m n) → P (fold _•_ e M)
    fold-⊎presʳ pres Pe {zero}  M = Pe
    fold-⊎presʳ pres Pe {suc m} M = TableP.foldr-⊎presʳ
      P pres (fold-⊎presʳ pres Pe (M ∘ fsuc)) (M fzero)


  -- Properties of fold⁺

  module _ {a p} {A : Set a} (P : Pred A p) {_•_ : Op₂ A} where
  
    fold⁺-×pres : _•_ Preservesᵇ P → ∀ {m n} {M : Matrix A (suc m) (suc n)} →
                  All P M → P (fold⁺ _•_ M)
    fold⁺-×pres •-pres-P {zero} PM  = TableP.foldr⁺-×pres P •-pres-P (PM fzero)
    fold⁺-×pres •-pres-P {suc m} PM = •-pres-P (TableP.foldr⁺-×pres P •-pres-P (PM fzero)) (fold⁺-×pres •-pres-P (PM ∘ fsuc))

    fold⁺-⊎pres : _•_ Preservesᵒ P → ∀ {m n} {M : Matrix A (suc m) (suc n)} →
                  Any P M → P (fold⁺ _•_ M)
    fold⁺-⊎pres pres {zero}  (fzero , PM₀) = TableP.foldr⁺-⊎pres P pres PM₀
    fold⁺-⊎pres pres {zero}  (fsuc () , _)
    fold⁺-⊎pres pres {suc m} (fzero , PM₀) = pres _ _ (inj₁ (TableP.foldr⁺-⊎pres P pres PM₀))
    fold⁺-⊎pres pres {suc m} (fsuc i , PMᵢ) = pres _ _ (inj₂ (fold⁺-⊎pres pres (i , PMᵢ))) --fold-⊎pres P pres _ (i , PMᵢ)



  -- Properties of min

  x≤min⁺[M] : ∀ {m n} {M : Matrix ℕ (suc m) (suc n)} → ∀ {x} → All (x ≤_) M → x ≤ min⁺ M
  x≤min⁺[M] = fold⁺-×pres (_ ≤_) m≤n×m≤o⇒m≤n⊓o
  
  min⁺[M]≤x : ∀ {m n} (M : Matrix ℕ (suc m) (suc n)) → ∀ {x} → Any (_≤ x) M → min⁺ M ≤ x
  min⁺[M]≤x _ = fold⁺-⊎pres (_≤ _) n≤m⊎o≤m⇒n⊓o≤m

  min⁺[M]≤M : ∀ {m n} (M : Matrix ℕ (suc m) (suc n)) → All (min⁺ M ≤_) M
  min⁺[M]≤M M i j = min⁺[M]≤x M (i , j , ≤-refl)
  
  min⁺[M]<x : ∀ {m n} (M : Matrix ℕ (suc m) (suc n)) → ∀ {x} → Any (_< x) M → min⁺ M < x
  min⁺[M]<x _ = fold⁺-⊎pres (_< _) n<m⊎o<m⇒n⊓o<m
  
  min⁺[M]≡x : ∀ {x} {m n} {M : Matrix ℕ (suc m) (suc n)} → x ∈ M → All (x ≤_) M → min⁺ M ≡ x
  min⁺[M]≡x {M = M} (i , j , x≈Mᵢⱼ) x≤M = ≤-antisym (min⁺[M]≤x M (i , j , ≤-reflexive (sym x≈Mᵢⱼ))) (x≤min⁺[M] x≤M)
  
  min⁺-constant : ∀ {m n} {M : Matrix ℕ (suc m) (suc n)} → ∀ {x} → All (_≡ x) M → min⁺ M ≡ x
  min⁺-constant = fold⁺-×pres (_≡ _) ⊓-preserves-≡x

  min⁺-cong : ∀ {m n} {M N : Matrix ℕ (suc m) (suc n)} →
              Pointwise _≡_ M N → min⁺ M ≡ min⁺ N
  min⁺-cong = fold⁺-cong {_~_ = _≡_} (cong₂ _⊓_)
  
  min⁺[M]<min⁺[N] : ∀ {m n p q} {M : Matrix ℕ (suc m) (suc n)} {N : Matrix ℕ (suc p) (suc q)} →
                    All (λ y → Any (_< y) M) N → min⁺ M < min⁺ N
  min⁺[M]<min⁺[N] {p = zero}  {zero}  M<N = min⁺[M]<x _ (M<N fzero fzero)
  min⁺[M]<min⁺[N] {p = zero}  {suc q} M<N = m<n×m<o⇒m<n⊓o (min⁺[M]<x _ (M<N fzero fzero)) (min⁺[M]<min⁺[N] (λ i j → M<N i (fsuc j)))
  min⁺[M]<min⁺[N] {p = suc p} {zero}  M<N = m<n×m<o⇒m<n⊓o (min⁺[M]<x _ (M<N fzero fzero)) (min⁺[M]<min⁺[N] (λ i j → M<N (fsuc i) j))
  min⁺[M]<min⁺[N] {p = suc p} {suc q} M<N = m<n×m<o⇒m<n⊓o (m<n×m<o⇒m<n⊓o (min⁺[M]<x _ (M<N fzero fzero)) (min⁺[M]<min⁺[N] {p = 0} (λ i j → M<N fzero (fsuc j)))) (min⁺[M]<min⁺[N] (λ i j → M<N (fsuc i) j))
              


  max⁺-cong : ∀ {m n} {t s : Matrix ℕ (suc m) (suc n)} →
              Pointwise _≡_ t s → max⁺ t ≡ max⁺ s
  max⁺-cong = fold⁺-cong {_~_ = _≡_} (cong₂ _⊔_)

  x≤max⁺[M] : ∀ {m n} (M : Matrix ℕ (suc m) (suc n)) →
              ∀ {x} → Any (x ≤_) M → x ≤ max⁺ M 
  x≤max⁺[M] _ = fold⁺-⊎pres (_ ≤_) m≤n⊎m≤o⇒m≤n⊔o

  max⁺[M]≤x : ∀ {m n} {M : Matrix ℕ (suc m) (suc n)} →
              ∀ {x} → All (_≤ x) M → max⁺ M ≤ x
  max⁺[M]≤x = fold⁺-×pres (_≤ _) n≤m×o≤m⇒n⊔o≤m

  M≤max⁺[M] : ∀ {m n} (M : Matrix ℕ (suc m) (suc n)) → All (_≤ max⁺ M) M
  M≤max⁺[M] M i j = x≤max⁺[M] M (i , j , ≤-refl)

  max⁺-constant : ∀ {m n} {M : Matrix ℕ (suc m) (suc n)} →
                  ∀ {x} → All (_≡ x) M → max⁺ M ≡ x
  max⁺-constant {x = x} = fold⁺-×pres (_≡ x) ⊔-preserves-≡x
  
  max⁺[M]≡x : ∀ {x} {m n} {M : Matrix ℕ (suc m) (suc n)} → x ∈ M → All (_≤ x) M → max⁺ M ≡ x
  max⁺[M]≡x {M = M} (i , j , x≈Mᵢⱼ) M≤x = ≤-antisym (max⁺[M]≤x M≤x) (x≤max⁺[M] M (i , j , ≤-reflexive x≈Mᵢⱼ))

  zipWith-sym : ∀ {a b ℓ} {A : Set a} {B : Set b} (_≈_ : Rel B ℓ)
                {f : A → A → B} → (∀ x y → f x y ≈ f y x) →
                ∀ {m n} (s t : Matrix A m n) → Pointwise _≈_ (zipWith f s t) (zipWith f t s)
  zipWith-sym _ sym s t i j = sym (s i j) (t i j)
