open import Data.Nat using (ℕ; zero; suc; _≤_; _<_)
open import Data.Nat.Properties using (⊔-sel; ≤-antisym; ≤-reflexive)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_,_; proj₂)
open import Function using (_∘_)
open import Relation.Binary using (Rel; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Unary using (Pred)
open import Algebra.FunctionProperties using (Op₂; Selective)

open import RoutingLib.Data.Matrix
open import RoutingLib.Data.Matrix.Relation.Pointwise using (Pointwise)
open import RoutingLib.Data.Matrix.Membership.Propositional using (_∈_)
open import RoutingLib.Data.Nat.Properties
open import RoutingLib.Data.Table using (Table)
open import RoutingLib.Data.Table.All using () renaming (All to TableAll)
import RoutingLib.Data.Table.Properties as TableP
open import RoutingLib.Algebra.FunctionProperties

module RoutingLib.Data.Matrix.Properties where

  -- Properties fold

  module _ {a p} {A : Set a} (P : Pred A p) {_•_ : Op₂ A} where
  
    fold-×pres : _•_ ×-Preserves P → ∀ {e : A} → P e →
                        ∀ {m n} {M : Matrix A m n} → All P M →
                        P (fold _•_ e M)
    fold-×pres pres Pe {zero}  PM = Pe
    fold-×pres pres Pe {suc m} PM = TableP.foldr-×pres P pres
      (fold-×pres pres Pe (PM ∘ fsuc)) (PM fzero)

    postulate fold-⊎pres : _•_ ⊎-Preserves P → ∀ e {m n} {M : Matrix A  m n} →
                         Any P M → P (fold _•_ e M)
    --fold-⊎pres = {!!}

    postulate fold-⊎presʳ : _•_ ⊎-Preservesʳ P → ∀ {e} → P e →
                        ∀ {m n} (M : Matrix A  m n) → P (fold _•_ e M)
    --fold-⊎presʳ = {!!}


  -- Properties of fold⁺

  module _ {a p} {A : Set a} (P : Pred A p) {_•_ : Op₂ A} where
  
    fold⁺-×pres : _•_ ×-Preserves P →
                         ∀ {m n} {M : Matrix A (suc m) (suc n)} →
                         All P M → P (fold⁺ _•_ M)
    fold⁺-×pres •-pres-P PM = fold-×pres P •-pres-P (TableP.foldr⁺-×pres P •-pres-P (PM fzero)) (PM ∘ fsuc)

    fold⁺-⊎pres : _•_ ⊎-Preserves P → ∀ {m n} {M : Matrix A (suc m) (suc n)} →
                         Any P M → P (fold⁺ _•_ M)
    fold⁺-⊎pres pres {M = M} (fzero  , PMᵢ) = fold-⊎presʳ P (⊎pres⇒⊎presʳ pres) (TableP.foldr⁺-⊎pres P pres PMᵢ) (M ∘ fsuc)
    fold⁺-⊎pres pres {M = M} (fsuc i , PMᵢ) = fold-⊎pres P pres _ (i , PMᵢ)






  -- Properties of min

  x≤min⁺[M] : ∀ {m n} {M : Matrix ℕ (suc m) (suc n)} → ∀ {x} → All (x ≤_) M → x ≤ min⁺ M
  x≤min⁺[M] = fold⁺-×pres (_ ≤_) m≤n×m≤o⇒m≤n⊓o
  
  min⁺[M]≤x : ∀ {m n} (M : Matrix ℕ (suc m) (suc n)) → ∀ {x} → Any (_≤ x) M → min⁺ M ≤ x
  min⁺[M]≤x _ = fold⁺-⊎pres (_≤ _) n≤m⊎o≤m⇒n⊓o≤m

  min⁺[M]≡x : ∀ {x} {m n} {M : Matrix ℕ (suc m) (suc n)} → x ∈ M → All (x ≤_) M → min⁺ M ≡ x
  min⁺[M]≡x {M = M} (i , j , x≈Mᵢⱼ) x≤M = ≤-antisym (min⁺[M]≤x M (i , j , ≤-reflexive (sym x≈Mᵢⱼ))) (x≤min⁺[M] x≤M)
  
  min⁺-constant : ∀ {m n} {M : Matrix ℕ (suc m) (suc n)} → ∀ {x} → All (_≡ x) M → min⁺ M ≡ x
  min⁺-constant = fold⁺-×pres (_≡ _) ⊓-preserves-≡x

  postulate min⁺[M]<min⁺[N] : ∀ {m n} {M N : Matrix ℕ (suc m) (suc n)} →
                              All (λ y → Any (_< y) M) N → min⁺ M < min⁺ N

  postulate min⁺-cong : ∀ {m n} {t s : Matrix ℕ (suc m) (suc n)} →
              Pointwise _≡_ t s → min⁺ t ≡ min⁺ s
              


  postulate max⁺-cong : ∀ {m n} {t s : Matrix ℕ (suc m) (suc n)} →
              Pointwise _≡_ t s → max⁺ t ≡ max⁺ s

  postulate M≤max⁺ : ∀ {m n} (M : Matrix ℕ (suc m) (suc n)) → All (_≤ max⁺ M) M

  postulate max⁺[M]≤x : ∀ {m n} {M : Matrix ℕ (suc m) (suc n)} →
                          ∀ {x} → All (_≤ x) M → max⁺ M ≤ x

  max⁺-constant : ∀ {m n} {M : Matrix ℕ (suc m) (suc n)} →
                  ∀ {x} → All (_≡ x) M → max⁺ M ≡ x
  max⁺-constant {x = x} = fold⁺-×pres (_≡ x) ⊔-preserves-≡x
  
  postulate max⁺[M]≡x : ∀ {x} {m n} {M : Matrix ℕ (suc m) (suc n)} → x ∈ M → All (_≤ x) M → max⁺ M ≡ x

  zipWith-sym : ∀ {a b ℓ} {A : Set a} {B : Set b} (_≈_ : Rel B ℓ)
                {f : A → A → B} → (∀ x y → f x y ≈ f y x) →
                ∀ {m n} (s t : Matrix A m n) → Pointwise _≈_ (zipWith f s t) (zipWith f t s)
  zipWith-sym _ sym s t i j = sym (s i j) (t i j)
