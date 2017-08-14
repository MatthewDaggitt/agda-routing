open import Data.Nat using (ℕ; suc; _≤_; _<_)
open import Data.Nat.Properties using (⊔-sel)
open import Relation.Binary using (Rel; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Algebra.FunctionProperties using (Op₂; Selective)

open import RoutingLib.Data.Matrix
open import RoutingLib.Data.Matrix.Relation.Pointwise using (Pointwise)
open import RoutingLib.Algebra.FunctionProperties

module RoutingLib.Data.Matrix.Properties where

{-
  foldrd-cong : ∀ {a b} {A : Set a} {B : Set b} {f : A → B → B}
                {d e} → d ≡ e →
                ∀ {m n} {s t : Matrix A m n} → Pointwise _≡_ s t →
                foldrd f d t ≡ foldrd f e s
  foldrd-cong refl = {!!}


  foldrd+-cong : ∀ {a} {A : Set a} {_•_ : Op₂ A} {m n} {t s : Matrix A (suc m) (suc n)} → Pointwise _≡_ s t → foldrd+ _•_ t ≡ foldrd+ _•_ s
  foldrd+-cong = {!!}
-}

  postulate foldʳᵈ+∈M : ∀ {a} {A : Set a} {_•_ : Op₂ A} → Selective _≡_ _•_ →
                          ∀ {m n} (M : Matrix A (suc m) (suc n)) → Any (foldʳᵈ+ _•_ M ≡_) M

  postulate foldʳᵈ+-×preserves : ∀ {a p} {A : Set a}
                                {P : A → Set p} _•_ → _•_ ×-Preserves P →
                                ∀ {m n} {M : Matrix A (suc m) (suc n)} →
                                All P M → P (foldʳᵈ+ _•_ M)
  --foldr-×preserves _    []         pe = pe
  --foldr-×preserves pres (px ∷ pxs) pe = pres px (foldr-×preserves pres pxs pe)
  
{-
  foldr-forces× : ∀ {p} {P : A → Set p} {_•_} → _•_ Forces-× P → ∀ e xs → P (foldr _•_ e xs) → All P xs
  foldr-forces× _          _ []       _     = []
  foldr-forces× •-forces-P _ (x ∷ xs) Pfold with •-forces-P Pfold
  ... | (px , pfxs) = px ∷ foldr-forces× •-forces-P _ xs pfxs

  
  
  foldr-⊎preservesᵣ : ∀ {p} {P : A → Set p} {_•_} → _•_ ⊎-Preservesᵣ P → ∀ {e} xs → P e → P (foldr _•_ e xs)
  foldr-⊎preservesᵣ •-pres-P []       Pe = Pe
  foldr-⊎preservesᵣ •-pres-P (_ ∷ xs) Pe = •-pres-P _ (foldr-⊎preservesᵣ •-pres-P xs Pe)

  foldr-⊎preserves : ∀ {p} {P : A → Set p} {_•_} → _•_ ⊎-Preserves P → ∀ {xs} e → Any P xs → P (foldr _•_ e xs)
  foldr-⊎preserves (presₗ , presᵣ) e (here px)   = presₗ _ px
  foldr-⊎preserves (presₗ , presᵣ) e (there pxs) = presᵣ _ (foldr-⊎preserves (presₗ , presᵣ) e pxs)
-}

  postulate min+-cong : ∀ {m n} {t s : Matrix ℕ (suc m) (suc n)} →
              Pointwise _≡_ t s → min+ t ≡ min+ s

  postulate ≤M⇒min+≤M : ∀ {m n} {M : Matrix ℕ (suc m) (suc n)} →
                          ∀ {x} → All (x ≤_) M → x ≤ min+ M
                          
  postulate min+[M]≤x : ∀ {m n} (M : Matrix ℕ (suc m) (suc n)) →
                        ∀ {x} → Any (_≤ x) M → min+ M ≤ x

  postulate min+-constant : ∀ {m n} {M : Matrix ℕ (suc m) (suc n)} →
                            ∀ {x} → All (_≡ x) M → min+ M ≡ x

  postulate min+[M]<min+[N] : ∀ {m n} {M N : Matrix ℕ (suc m) (suc n)} →
                              All (λ y → Any (_< y) M) N → min+ M < min+ N


  postulate min+∈M : ∀ {m n} (M : Matrix ℕ (suc m) (suc n)) → Any (min+ M ≡_) M
  

  postulate max+-cong : ∀ {m n} {t s : Matrix ℕ (suc m) (suc n)} →
              Pointwise _≡_ t s → max+ t ≡ max+ s
  --max+-cong t≡s = {!!}

  postulate M≤max+ : ∀ {m n} (M : Matrix ℕ (suc m) (suc n)) → All (_≤ max+ M) M
  --Mᵢⱼ≤max+M M i j = {!!}

  postulate M≤⇒max+≤ : ∀ {m n} {M : Matrix ℕ (suc m) (suc n)} →
                          ∀ {x} → All (_≤ x) M → max+ M ≤ x

  postulate max+-constant : ∀ {m n} {M : Matrix ℕ (suc m) (suc n)} →
                            ∀ {x} → All (_≡ x) M → max+ M ≡ x
                            
  max+∈M : ∀ {m n} (M : Matrix ℕ (suc m) (suc n)) → Any (max+ M ≡_) M
  max+∈M = foldʳᵈ+∈M ⊔-sel

  postulate max+≡Mᵢⱼ : ∀ {m n} {M : Matrix ℕ (suc m) (suc n)} {i j} → All (_≤ M i j) M → max+ M ≡ M i j



  zipWith-sym : ∀ {a b ℓ} {A : Set a} {B : Set b} (_≈_ : Rel B ℓ)
                {f : A → A → B} → (∀ x y → f x y ≈ f y x) →
                ∀ {m n} (s t : Matrix A m n) → Pointwise _≈_ (zipWith f s t) (zipWith f t s)
  zipWith-sym _ sym s t i j = sym (s i j) (t i j)

  --postulate zipWith-cong : ∀ {a b ℓ} {A : Set a} {B : Set b} {m n} {M N P Q : Matrix ℕ (suc m) (suc n)} {f Preserves₂ _≈₁_ ⟶ _≈₂_ ⟶ _≈₃_ → Pointwise _≈₁_ M P → Pointwise _≈₂_ N Q → Pointwise _≈₃_ (zipWith M N) (zipWith P Q)
