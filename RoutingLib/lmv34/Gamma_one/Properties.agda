{-# OPTIONS --allow-unsolved-metas #-}
open import Algebra.FunctionProperties
open import Data.Bool.Base using (true; false)
open import Data.Fin renaming (zero to fzero; suc to fsuc) hiding (_≤_; _≟_)
open import Data.Fin.Properties using (<-cmp; <-respˡ-≡; <-respʳ-≡; <-asym) renaming (≡-setoid to Fin-setoid)
open import Data.Fin.Patterns
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; filter; tabulate; map; foldr)
open import Data.List.Properties using (map-tabulate; filter-none)
open import Data.List.Relation.Binary.Permutation.Inductive
  using ()
  renaming (_↭_ to _≡-↭_; refl to ≡-refl; prep to ≡-prep; trans to ≡-trans; swap to ≡-swap)
import Data.List.Relation.Binary.Permutation.Setoid.Properties as PermProperties
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
import Data.List.Relation.Binary.Equality.Setoid as Equality
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ₐ; _∷_ to _∷ₐ_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_; yes; no; does; proof; _because_; ofʸ; ofⁿ)
open import Relation.Nullary.Negation using (¬?; contradiction; contraposition)
open import Relation.Unary using (Pred; Decidable; ∁)
open import Function using (_∘_)
open import Relation.Binary using (IsEquivalence; Setoid; DecSetoid; DecTotalOrder; Rel; _Respects_; _⇒_; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
import Relation.Binary.EqReasoning as EqReasoning

open import RoutingLib.Iteration.Synchronous using (_^_; IsFixedPoint)
open import RoutingLib.Data.List using (insert)
import RoutingLib.Data.List.Sorting as Sorting
import RoutingLib.Data.List.Sorting.InsertionSort as InsertionSort
open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
open import RoutingLib.Routing as Routing using (AdjacencyMatrix)
open import RoutingLib.Data.Matrix using (SquareMatrix)
import RoutingLib.lmv34.Gamma_zero as Gamma_zero
import RoutingLib.lmv34.Gamma_zero.Algebra as Gamma_zero_Algebra
import RoutingLib.lmv34.Gamma_one as Gamma_one
import RoutingLib.lmv34.Gamma_one.Algebra as Gamma_one_Algebra

module RoutingLib.lmv34.Gamma_one.Properties
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  {n} (A : AdjacencyMatrix algebra n)
  where

open RawRoutingAlgebra algebra
open IsRoutingAlgebra isRoutingAlgebra
open Routing algebra n renaming (I to M)
open Gamma_zero algebra A
open Gamma_zero_Algebra algebra n
open Gamma_one isRoutingAlgebra A
open Gamma_one_Algebra isRoutingAlgebra n

open Setoid (Fin-setoid n) using () renaming (refl to Fin-refl; sym to Fin-sym)
open DecSetoid FinRoute-decSetoid
  using ()
  renaming (_≈_ to _≈ᵣ_; refl to ≈ᵣ-refl; trans to ≈ᵣ-trans; sym to ≈ᵣ-sym)
open DecTotalOrder decTotalOrder using (≤-respˡ-≈; ≤-respʳ-≈; total; _≤_) renaming (antisym to ≤-antisym; refl to ≤-refl; trans to ≤-trans)
open InsertionSort decTotalOrder using (sort; sort↗) renaming (sort↭ to sort≡-↭)
open Sorting _≤_ using (Sorted)
open Equality FinRoute-setoid using (_≋_; ≋-refl; ≋-sym; ≋-trans)
open PermProperties FinRoute-setoid using (≋⇒↭)

------------------------------------
-- Operation properties

postulate
  f-cong : ∀ (f : Route → Route) {s s' : Route} → s ≈ s' → f s ≈ f s' -- need this to prove []-cong
  f-fix : ∀ (f : Route → Route) → f ∞# ≈ ∞# -- need this to prove ~-lemma

insert-min : ∀ {x xs} → All (x ≤_) xs → insert total x xs ≋ (x ∷ xs)
insert-min {x} {[]} x≤xs = ≋-refl
insert-min {x} {y ∷ xs} (x≤y¹ All.∷ x≤xs) with total x y
... | inj₁ x≤y² = ≋-refl
... | inj₂ y≤x  = (≈ᵣ-sym x=y) Pointwise.∷ (≋-trans (insert-min x≤xs) (x=y Pointwise.∷ ≋-refl))
  where
    x=y : x ≈ᵣ y
    x=y = ≤-antisym x≤y¹ y≤x

All-≤-preserves-≈ᵣ : ∀ {x x' xs} → x ≈ᵣ x' → All (x ≤_) xs → All (x' ≤_) xs
All-≤-preserves-≈ᵣ x=x' All.[] = All.[]
All-≤-preserves-≈ᵣ x=x' (x≤y All.∷ x≤xs) = (≤-respˡ-≈ x=x' x≤y) All.∷ (All-≤-preserves-≈ᵣ x=x' x≤xs)

All-≤-trans : ∀ {xs x y} → x ≤ y → All (y ≤_) xs → All (x ≤_) xs
All-≤-trans x≤y All.[] = All.[]
All-≤-trans x≤y (y≤x₁ All.∷ y≤xs) = (≤-trans x≤y y≤x₁) All.∷ All-≤-trans x≤y y≤xs

insert-≤ : ∀ {x y ys} → x ≤ y → insert total x (y ∷ ys) ≋ x ∷ y ∷ ys
insert-≤ {x} {y} {[]} x≤y with total x y
... | inj₁ x≤y' = ≋-refl
... | inj₂ y≤x  = (≤-antisym y≤x x≤y) Pointwise.∷ ((≤-antisym x≤y y≤x) Pointwise.∷ Pointwise.[])
insert-≤ {x} {y} {z ∷ zs} x≤y with total x y
... | inj₁ x≤y' = ≋-refl
... | inj₂ y≤x  = prf
  where prf : y ∷ (insert total x (z ∷ zs)) ≋ x ∷ y ∷ z ∷ zs
        prf with total x z
        ... | inj₁ x≤z = (≤-antisym y≤x x≤y) Pointwise.∷ ((≤-antisym x≤y y≤x) Pointwise.∷ ≋-refl)
        ... | inj₂ z≤x = {!!} -- y ∷ z ∷ insert total x zs ≋ x y z zs

insert-≋ : ∀ {x x' xs xs'} → x ≈ᵣ x' → Sorted xs → Sorted xs' → xs ≋ xs' →
            insert total x xs ≋ insert total x' xs'
insert-≋ x=x' sxs sxs' Pointwise.[] = x=x' Pointwise.∷ Pointwise.[]
insert-≋ {x₁} {x₁'} {x₂ ∷ xs} {x₂' ∷ xs'}
          x₁=x₁' (x₂≤xs AllPairs.∷ sxs) (x₂'≤xs' AllPairs.∷ sxs') (x₂=x₂' Pointwise.∷ xs=xs') with
      total x₁ x₂ | total x₁' x₂'
... | inj₁ x₁≤x₂ | inj₁ x₁'≤x₂' = x₁=x₁' Pointwise.∷ x₂=x₂' Pointwise.∷ xs=xs'
... | inj₂ x₂≤x₁ | inj₂ x₂'≤x₁' = x₂=x₂' Pointwise.∷ (insert-≋ x₁=x₁' sxs sxs' xs=xs')
... | inj₁ x₁≤x₂ | inj₂ x₂'≤x₁' = x₁=x₂' Pointwise.∷ (≋-trans (x₂=x₁' Pointwise.∷ xs=xs') (≋-sym (insert-min (All-≤-preserves-≈ᵣ x₂'=x₁' x₂'≤xs'))))
                                  where
                                    x₁=x₂ : x₁ ≈ᵣ x₂
                                    x₁=x₂ = ≤-antisym x₁≤x₂ (≤-respˡ-≈ (≈ᵣ-sym x₂=x₂') (≤-respʳ-≈ (≈ᵣ-sym x₁=x₁') x₂'≤x₁'))
                                    x₁=x₂' : x₁ ≈ᵣ x₂'
                                    x₁=x₂' = ≈ᵣ-trans x₁=x₂ x₂=x₂'
                                    x₂'=x₁' : x₂' ≈ᵣ x₁'
                                    x₂'=x₁' = ≈ᵣ-trans (≈ᵣ-sym x₁=x₂') x₁=x₁'
                                    x₂=x₁' : x₂ ≈ᵣ x₁'
                                    x₂=x₁' = ≈ᵣ-trans x₂=x₂' x₂'=x₁'
... | inj₂ x₂≤x₁ | inj₁ x₁'≤x₂' = x₂=x₁' Pointwise.∷ ≋-trans (insert-min (All-≤-preserves-≈ᵣ x₂=x₁ x₂≤xs)) (x₁=x₂' Pointwise.∷ xs=xs')
                                  where
                                    x₁'=x₂' : x₁' ≈ᵣ x₂'
                                    x₁'=x₂' = ≤-antisym x₁'≤x₂' (≤-respˡ-≈ x₂=x₂' (≤-respʳ-≈ x₁=x₁' x₂≤x₁))
                                    x₂=x₁' : x₂ ≈ᵣ x₁'
                                    x₂=x₁' = ≈ᵣ-trans x₂=x₂' (≈ᵣ-sym x₁'=x₂')
                                    x₁=x₂' : x₁ ≈ᵣ x₂'
                                    x₁=x₂' = ≈ᵣ-trans x₁=x₁' (≈ᵣ-trans (≈ᵣ-sym x₂=x₁') x₂=x₂')
                                    x₂=x₁ : x₂ ≈ᵣ x₁
                                    x₂=x₁ = ≈ᵣ-trans x₂=x₁' (≈ᵣ-sym x₁=x₁')

double-insert : ∀ {x y xs} → Sorted xs →
                insert total x (insert total y xs) ≋ insert total y (insert total x xs)
double-insert {x} {y} {[]} _ with
      total x y | total y x
... | inj₁ x≤y  | inj₁ y≤x¹ = (≤-antisym x≤y y≤x¹) Pointwise.∷ (≤-antisym y≤x¹ x≤y) Pointwise.∷ Pointwise.[]
... | inj₁ x≤y  | inj₂ x≤y¹ = ≋-refl
... | inj₂ y≤x  | inj₁ y≤x¹ = ≋-refl
... | inj₂ y≤x  | inj₂ x≤y¹ = (≤-antisym y≤x x≤y¹) Pointwise.∷ (≤-antisym x≤y¹ y≤x) Pointwise.∷ Pointwise.[]
double-insert {x} {y} {z ∷ xs} (z≤xs AllPairs.∷ sxs) with
      total y z | total x z
... | inj₁ y≤z  | inj₁ x≤z = prf
  where
    prf : insert total x (y ∷ z ∷ xs) ≋ insert total y (x ∷ z ∷ xs)
    prf with
          total x y | total y x
    ... | inj₁ x≤y  | inj₁ y≤x¹ = ≤-antisym x≤y y≤x¹ Pointwise.∷ ≤-antisym y≤x¹ x≤y Pointwise.∷ ≈ᵣ-refl Pointwise.∷ ≋-refl
    ... | inj₁ x≤y  | inj₂ x≤y¹ = ≈ᵣ-refl Pointwise.∷ (≋-sym (insert-min (All-≤-trans y≤z (≤-refl All.∷ z≤xs))))
    ... | inj₂ y≤x  | inj₁ y≤x¹ = ≈ᵣ-refl Pointwise.∷ (insert-min (All-≤-trans x≤z (≤-refl All.∷ z≤xs)))
    ... | inj₂ y≤x  | inj₂ x≤y¹ = (≤-antisym y≤x x≤y¹) Pointwise.∷ (insert-≋ (≤-antisym x≤y¹ y≤x) (z≤xs AllPairs.∷ sxs) (z≤xs AllPairs.∷ sxs) ≋-refl)
... | inj₁ y≤z  | inj₂ z≤x = prf
  where
    prf : insert total x (y ∷ z ∷ xs) ≋ insert total y (z ∷ (insert total x xs))
    prf with total x y | total y z
    ... | inj₁ x≤y | _ = {!!} -- x ∷ y ∷ z ∷ xs = insert total 
    ... | inj₂ y≤x | inj₁ y≤z = prf'
      where
      prf' : y ∷ (insert total x (z ∷ xs)) ≋ y ∷ z ∷ (insert total x xs)
      prf' with total x z
      ... | inj₁ x≤z = {!!}
      ... | inj₂ z≤x = ≋-refl
    ... | inj₂ y≤x | inj₂ z≤y = {!!}
... | inj₂ z≤y  | inj₁ x≤z = prf
  where
    prf : insert total x (z ∷ (insert total y xs)) ≋ insert total y (x ∷ z ∷ xs)
    prf = {!!}
... | inj₂ z≤y  | inj₂ z≤x = prf
  where
    prf : insert total x (z ∷ (insert total y xs)) ≋ insert total y (z ∷ (insert total x xs))
    prf with
          total x z | total y z
    ... | inj₁ x≤z  | inj₁ y≤z = x=y Pointwise.∷ ≈ᵣ-refl
                                    Pointwise.∷ ≋-trans (insert-min (All-≤-trans y≤z z≤xs))
                                               (≋-trans (≈ᵣ-sym x=y Pointwise.∷ ≋-refl)
                                                        (≋-sym (insert-min (All-≤-trans x≤z z≤xs))))
                                where
                                  x=y : x ≈ᵣ y
                                  x=y = ≤-antisym (≤-trans x≤z z≤y) (≤-trans y≤z z≤x)
    ... | inj₁ x≤z  | inj₂ z≤y = {!!}
    ... | inj₂ z≤x  | inj₁ y≤z = {!!}
    ... | inj₂ z≤x  | inj₂ z≤y = ≈ᵣ-refl Pointwise.∷ double-insert sxs


-- build transitive equational reasoning for pointwise equality ≋.

sort-swap : ∀ x y xs → sort (x ∷ y ∷ xs) ≋ sort (y ∷ x ∷ xs)
sort-swap x y xs = double-insert {x} {y} {sort xs} (sort↗ xs)

{-# TERMINATING #-}
sort-↭-≋ : ∀ {xs ys} → xs ↭ ys → sort xs ≋ sort ys
sort-↭-≋ refl = ≋-refl
sort-↭-≋ {x ∷ xs} {y ∷ ys} (prep x=y xs=ys) = insert-≋ x=y (sort↗ xs) (sort↗ ys) (sort-↭-≋ xs=ys)
sort-↭-≋ (trans xs=ys ys=zs) = ≋-trans (sort-↭-≋ xs=ys) (sort-↭-≋ ys=zs)
sort-↭-≋ {x₁ ∷ x₂ ∷ xs} {x₂' ∷ x₁' ∷ xs'} (swap x₁=x₁' x₂=x₂' xs=xs') = ≋-trans (sort-swap x₁ x₂ xs) (sort-↭-≋ (prep x₂=x₂' (prep x₁=x₁' xs=xs')))

mergeSorted-cong : ∀ {A A' B B'} → A ≋ A' → B ≋ B' →
                   mergeSorted A B ≋ mergeSorted A' B'
mergeSorted-cong Pointwise.[] B=B' = B=B'
mergeSorted-cong (x∼y Pointwise.∷ A=A') Pointwise.[] = x∼y Pointwise.∷ A=A'
mergeSorted-cong {(d₁ , v₁) ∷ A} {(d₁' , v₁') ∷ A'} {(d₂ , v₂) ∷ B} {(d₂' , v₂') ∷ B'}
                 ((d₁=d₁' , v₁=v₁') Pointwise.∷ A=A') ((d₂=d₂' , v₂=v₂') Pointwise.∷ B=B') with
      <-cmp d₁ d₂     | <-cmp d₁' d₂'
... | tri< _ _ _     | tri< _ _ _       = (d₁=d₁' , v₁=v₁') Pointwise.∷ (mergeSorted-cong A=A' ((d₂=d₂' , v₂=v₂') Pointwise.∷ B=B'))
... | tri< d₁<d₂ _ _  | tri≈ ¬d₁'<d₂' _ _ = contradiction (<-respʳ-≡ d₂=d₂' (<-respˡ-≡ d₁=d₁' d₁<d₂)) ¬d₁'<d₂'
... | tri< d₁<d₂ _ _  | tri> ¬d₁'<d₂' _ _ = contradiction (<-respʳ-≡ d₂=d₂' (<-respˡ-≡ d₁=d₁' d₁<d₂)) ¬d₁'<d₂'
... | tri≈ ¬d₁<d₂ _ _ | tri< d₁'<d₂' _ _  = contradiction (<-respʳ-≡ (Fin-sym d₂=d₂') (<-respˡ-≡ (Fin-sym d₁=d₁') d₁'<d₂')) ¬d₁<d₂
... | tri≈ _ _ _     | tri≈ _ _ _       = (d₁=d₁' , ⊕-cong v₁=v₁' v₂=v₂') Pointwise.∷ mergeSorted-cong A=A' B=B'
... | tri≈ _ _ ¬d₂<d₁ | tri> _ _ d₂'<d₁'  = contradiction (<-respʳ-≡ (Fin-sym d₁=d₁') (<-respˡ-≡ (Fin-sym d₂=d₂') d₂'<d₁')) ¬d₂<d₁
... | tri> ¬d₁<d₂ _ _ | tri< d₁'<d₂' _ _  = contradiction (<-respʳ-≡ (Fin-sym d₂=d₂') (<-respˡ-≡ (Fin-sym d₁=d₁') d₁'<d₂')) ¬d₁<d₂
... | tri> _ _ d₂<d₁  | tri≈ _ _ ¬d₂'<d₁' = contradiction (<-respʳ-≡ d₁=d₁' (<-respˡ-≡ d₂=d₂' d₂<d₁)) ¬d₂'<d₁'
... | tri> _ _ _     | tri> _ _ _       = (d₂=d₂' , v₂=v₂') Pointwise.∷ mergeSorted-cong ((d₁=d₁' , v₁=v₁') Pointwise.∷ A=A') B=B'

⊕ₛ-cong : Congruent₂ _↭_ _⊕ₛ_
⊕ₛ-cong A=A' B=B' = ≋⇒↭ (mergeSorted-cong (sort-↭-≋ A=A') (sort-↭-≋ B=B'))

≡-↭⇒↭ : ∀ {xs ys} → xs ≡-↭ ys → xs ↭ ys
≡-↭⇒↭ ≡-refl = refl
≡-↭⇒↭ (≡-prep x xs=ys) = prep ≈ᵣ-refl (≡-↭⇒↭ xs=ys)
≡-↭⇒↭ (≡-swap x y xs=ys) = swap ≈ᵣ-refl ≈ᵣ-refl (≡-↭⇒↭ xs=ys)
≡-↭⇒↭ (≡-trans xs=ys ys=zs) = trans (≡-↭⇒↭ xs=ys) (≡-↭⇒↭ ys=zs)

sort↭ : ∀ {xs} → sort xs ↭ xs
sort↭ {xs} = ≡-↭⇒↭ (sort≡-↭ xs)

sort-cons : ∀ x xs → sort (x ∷ xs) ↭ x ∷ (sort xs)
sort-cons x [] = ↭-refl
sort-cons x (y ∷ xs) with total x y
... | inj₁ x≤y = {!!}
... | inj₂ y≤x = {!!}

sort-cong : Congruent₁ _↭_ sort
sort-cong {A} {A'} A=A' = begin
  sort A ↭⟨ sort↭ {A} ⟩
  A      ↭⟨ A=A' ⟩
  A'     ↭⟨ ↭-sym (sort↭ {A'}) ⟩
  sort A' ∎
  where open PermutationReasoning

mergeSorted-identityₗ : LeftIdentity _↭_ Ø mergeSorted
mergeSorted-identityₗ A = ↭-refl

mergeSorted-identityᵣ : RightIdentity _↭_ Ø mergeSorted
mergeSorted-identityᵣ [] = ↭-refl
mergeSorted-identityᵣ (x ∷ A) = ↭-refl

⊕ₛ-identityₗ : LeftIdentity _↭_ Ø _⊕ₛ_
⊕ₛ-identityₗ A = sort↭ {A}

⊕ₛ-identityᵣ : RightIdentity _↭_ Ø _⊕ₛ_
⊕ₛ-identityᵣ A = ↭-trans (mergeSorted-identityᵣ (sort A)) (sort↭ {A})

mergeSorted-cons : ∀ x xs ys →
                   mergeSorted (x ∷ xs) ys ↭ x ∷ (mergeSorted xs ys)
mergeSorted-cons = {!!}

⊕ₛ-cons : ∀ x xs ys → (x ∷ xs) ⊕ₛ ys ↭ x ∷ (xs ⊕ₛ ys)
⊕ₛ-cons x xs ys = begin
  (x ∷ xs) ⊕ₛ ys                        ≡⟨⟩
  mergeSorted (sort (x ∷ xs)) (sort ys) ↭⟨ {!!} ⟩
  mergeSorted (x ∷ (sort xs)) (sort ys) ↭⟨ mergeSorted-cons x (sort xs) (sort ys) ⟩
  x ∷ (mergeSorted (sort xs) (sort ys)) ≡⟨⟩
  x ∷ (xs ⊕ₛ ys)                        ∎
  where open PermutationReasoning
  
⨁ₛ-cong : ∀ {k} → {f g : Fin k → RoutingSet} →
          (∀ {i} → f i ↭ g i) → ⨁ₛ f ↭ ⨁ₛ g
⨁ₛ-cong {zero} {f} {g} f=g = ↭-refl
⨁ₛ-cong {suc k} {f} {g} f=g = ⊕ₛ-cong f=g (⨁ₛ-cong {k} f=g)

⊕ᵥ-cong : Congruent₂ _≈ᵥ_ _⊕ᵥ_
⊕ᵥ-cong V=V' W=W' i = ⊕ₛ-cong (V=V' i) (W=W' i)

⊕ᵥ-identityₗ : LeftIdentity _≈ᵥ_ Øᵥ _⊕ᵥ_
⊕ᵥ-identityₗ A i = ⊕ₛ-identityₗ (A i)

⊕ᵥ-identityᵣ : RightIdentity _≈ᵥ_ Øᵥ _⊕ᵥ_
⊕ᵥ-identityᵣ A i = ⊕ₛ-identityᵣ (A i)

filter-cong : ∀ {A A' : RoutingSet} {p} {P : Pred (Fin n × Route) p} {P? : Decidable P} →
              P Respects _≈ᵣ_ → A ↭ A' → filter P? A ↭ filter P? A'
filter-cong P≈ refl = refl
filter-cong P≈ (trans A=A' A'=A'') = trans (filter-cong P≈ A=A') (filter-cong P≈ A'=A'')
filter-cong {x ∷ A} {x' ∷ A'} {P? = P?} P≈ (prep x=x' A=A') with
      P? x   | P? x'
... | yes Px | yes Px' = prep x=x' (filter-cong P≈ A=A')
... | yes Px | no ¬Px' = contradiction (P≈ x=x' Px) ¬Px'
... | no ¬Px | yes Px' = contradiction (P≈ (≈ᵣ-sym x=x') Px') ¬Px
... | no ¬Px | no ¬Px' = filter-cong P≈ A=A'
filter-cong {x ∷ y ∷ A} {y' ∷ x' ∷ A'} {P? = P?} P≈ (swap x=x' y=y' A=A') with
      P? x   | P? y'
... | no ¬Px | no ¬Py' = prf
    where
      prf : filter P? (y ∷ A) ↭ filter P? (x' ∷ A')
      prf with
            P? x' | P? y
      ... | no ¬Px' | no ¬Py = filter-cong P≈ A=A'
      ... | no ¬Px' | yes Py = contradiction (P≈ y=y' Py) ¬Py'
      ... | yes Px' | _      = contradiction (P≈ (≈ᵣ-sym x=x') Px') ¬Px
... | no ¬Px | yes Py' = prf
    where
      prf : filter P? (y ∷ A) ↭ y' ∷ filter P? (x' ∷ A')
      prf with
            P? x'   | P? y
      ... | no ¬Px' | no ¬Py = contradiction (P≈ (≈ᵣ-sym y=y') Py') ¬Py
      ... | no ¬Px' | yes Py = prep y=y' (filter-cong P≈ A=A')
      ... | yes Px' | _      = contradiction (P≈ (≈ᵣ-sym x=x') Px') ¬Px
... | yes Px | no ¬Py' = prf
    where
      prf : x ∷ filter P? (y ∷ A) ↭ filter P? (x' ∷ A')
      prf with
            P? x'   | P? y
      ... | no ¬Px' | _      = contradiction (P≈ x=x' Px) ¬Px'
      ... | yes Px' | no ¬Py = prep x=x' (filter-cong P≈ A=A')
      ... | yes Px' | yes Py = contradiction (P≈ y=y' Py) ¬Py'
... | yes Px | yes Py' = prf
    where
      prf : x ∷ filter P? (y ∷ A) ↭ y' ∷ filter P? (x' ∷ A')
      prf with
            P? x'   | P? y
      ... | no ¬Px' | _      = contradiction (P≈ x=x' Px) ¬Px'
      ... | yes Px' | no ¬Py = contradiction (P≈ (≈ᵣ-sym y=y') Py') ¬Py
      ... | yes Px' | yes Py = swap x=x' y=y' (filter-cong P≈ A=A')

†-respects-≈ᵣ : (λ {(d , v) → ¬ (v ≈ ∞#)}) Respects _≈ᵣ_
†-respects-≈ᵣ {d₁ , v₁} {d₂ , v₂} (d₁=d₂ , v₁=v₂) ¬v₁=∞# =
  λ v₂=∞# → contradiction (≈-trans (v₁=v₂) v₂=∞#) ¬v₁=∞#

†-cong : Congruent₁ _↭_ _†
†-cong A=A' = filter-cong †-respects-≈ᵣ A=A'

†-identity : Ø † ↭ Ø
†-identity = refl

†-cons-valid : ∀ x xs → (isValid x) → (x ∷ xs) † ≡ x ∷ (xs †)
†-cons-valid x xs valid = {!!}

†-cons-invalid : ∀ x xs → ¬ (isValid x) → (x ∷ xs) † ≡ xs †
†-cons-invalid x xs invalid with isValid? x
... | yes _ = {!!}
... | no _  = {!!}
  where prf : xs † ≡ xs †
        prf = {!!}

tabulate-cong : ∀ {k} → {f g : Fin k → Fin n × Route} →
        (∀ {i} → f i ≈ᵣ g i) → tabulate f ↭ tabulate g
tabulate-cong {zero} {f} {g} f=g = refl
tabulate-cong {suc k} {f} {g} f=g = prep f=g (tabulate-cong {k} f=g)

[]-cong : ∀ {f : Route → Route} {A A'} →
            A ↭ A' → f [ A ] ↭ f [ A' ]
[]-cong A=A' = †-cong (lemma A=A')
   where lemma : {A A' : RoutingSet} → {f : Route → Route} →
                 A ↭ A' → map₂ f A ↭ map₂ f A'
         lemma refl = refl
         lemma (trans A=A'' A''=A') = trans (lemma A=A'') (lemma A''=A')
         lemma {f = f} (prep (d=d' , v=v') A=A') = prep (d=d' , f-cong f v=v') (lemma A=A')
         lemma {f = f} (swap (d₁=d₁' , v₁=v₁') (d₂=d₂' , v₂=v₂')  A=A') =
                 swap ((d₁=d₁' , f-cong f v₁=v₁')) ((d₂=d₂' , f-cong f v₂=v₂')) (lemma A=A')

〚〛-cong : ∀ {V V'} → V ≈ᵥ V' → A 〚 V 〛 ≈ᵥ A 〚 V' 〛
〚〛-cong V=V' i = ⨁ₛ-cong (λ {q} → []-cong (V=V' q))

≈ₘ⇒≈ᵥ : ∀ {M M' : RoutingMatrix} → M ≈ₘ M' → ~ M ≈ᵥ ~ M'
(≈ₘ⇒≈ᵥ M=M') i = †-cong (tabulate-cong (λ {j} → (Fin-refl , M=M' i j)))

Γ₁-cong : Congruent₁ _≈ᵥ_ Γ₁
Γ₁-cong V=V' = ⊕ᵥ-cong (〚〛-cong V=V') (≈ₘ⇒≈ᵥ ≈ₘ-refl)

Γ₁-iter-cong : ∀ k → Congruent₁ _≈ᵥ_ (Γ₁ ^ k)
Γ₁-iter-cong zero    V=V' = V=V'
Γ₁-iter-cong (suc k) V=V' = Γ₁-cong (Γ₁-iter-cong k V=V')

------------------------------------
-- Theorems 

-- Lemma A.2
private
  postulate
  {-LemmaA₂ : ∀ (f g : Fin n → Route) →
           ((tabulate λ d → (d , f d)) †) ⊕ₛ ((tabulate λ d → (d , g d)) †) ↭
           (tabulate λ d → (d , f d ⊕ g d)) †-}
    lemma : ∀ (f g : Fin n → Route) → (tabulate λ d → (d , f d)) ⊕ₛ (tabulate λ d → (d , g d)) ↭ tabulate λ d → (d , f d ⊕ g d)

†-⊕ₛ-distributive : ∀ {xs ys} → (xs †) ⊕ₛ (ys †) ↭ (xs ⊕ₛ ys) †
†-⊕ₛ-distributive {[]} {ys} = begin
  (Ø †) ⊕ₛ (ys †) ≡⟨⟩
  Ø ⊕ₛ (ys †)      ↭⟨ ⊕ₛ-identityₗ (ys †) ⟩
  ys †             ↭⟨ †-cong (↭-sym (⊕ₛ-identityₗ ys)) ⟩
  (Ø ⊕ₛ ys) †      ∎
  where open PermutationReasoning
†-⊕ₛ-distributive {x ∷ xs} {ys} with isValid? x
... | yes valid = begin
  ((x ∷ xs) †) ⊕ₛ (ys †) ↭⟨ ⊕ₛ-cong {u = ys †} (↭-reflexive (†-cons-valid x xs valid)) ↭-refl ⟩
  (x ∷ xs †) ⊕ₛ (ys †)   ↭⟨ ⊕ₛ-cons x (xs †) (ys †) ⟩
  x ∷ ((xs †) ⊕ₛ (ys †)) <⟨ †-⊕ₛ-distributive {xs} {ys} ⟩
  x ∷ ((xs ⊕ₛ ys) †)     ↭⟨ ↭-sym (↭-reflexive (†-cons-valid x (xs ⊕ₛ ys) valid)) ⟩
  (x ∷ (xs ⊕ₛ ys)) †     ↭⟨ †-cong (↭-sym (⊕ₛ-cons x xs ys)) ⟩
  ((x ∷ xs) ⊕ₛ ys) † ∎
  where open PermutationReasoning
... | no invalid = begin
  ((x ∷ xs) †) ⊕ₛ (ys †) ↭⟨ ⊕ₛ-cong {u = ys †} (↭-reflexive (†-cons-invalid x xs invalid))  ↭-refl ⟩
  (xs †) ⊕ₛ (ys †)       ↭⟨ †-⊕ₛ-distributive {xs} {ys} ⟩
  (xs ⊕ₛ ys) †           ↭⟨ ↭-sym (↭-reflexive (†-cons-invalid x (xs ⊕ₛ ys) invalid)) ⟩
  (x ∷ (xs ⊕ₛ ys)) †     ↭⟨ †-cong (↭-sym (⊕ₛ-cons x xs ys)) ⟩
  ((x ∷ xs) ⊕ₛ ys) †     ∎
  where open PermutationReasoning

LemmaA₂ : ∀ (f g : Fin n → Route) →
          ((tabulate λ d → (d , f d)) †) ⊕ₛ ((tabulate λ d → (d , g d)) †) ↭
          (tabulate λ d → (d , f d ⊕ g d)) †
LemmaA₂ f g = begin
  ((tabulate λ d → (d , f d)) †) ⊕ₛ ((tabulate λ d → (d , g d)) †) ↭⟨ †-⊕ₛ-distributive {tabulate λ d → (d , f d)} {tabulate λ d → (d , g d)} ⟩
  ((tabulate λ d → (d , f d)) ⊕ₛ (tabulate λ d → (d , g d)))† ↭⟨ †-cong {(tabulate λ d → (d , f d)) ⊕ₛ (tabulate λ d → (d , g d))} (lemma f g) ⟩
  (tabulate λ d → (d , f d ⊕ g d)) † ∎
  where open PermutationReasoning

{-
((tabulate λ d → (d , f d)) †) ⊕ₛ ((tabulate λ d → (d , g d)) †) ↭ by distrib † over ⊕ₛ
((tabulate λ d → (d , f d)) ⊕ₛ (tabulate λ d → (d , g d)) )† ↭ by lemma (and †-cong)
(tabulate λ d → (d , f d ⊕ g d)) †

make lemma:
∀ {k} (f g : Fin k → Route)
(tabulate λ d → (d , f d)) ⊕ₛ (tabulate λ d → (d , g d)) ↭ by induction on k
tabulate λ d → (d , f d ⊕ g d)
-}


invalid-pair : ∀ d → (∁ isValid) (d , ∞#)
invalid-pair d = λ (p : isValid (d , ∞#)) → p ≈-refl

tabulate-none : ∀ {k} {a b} {A : Set a} {P : Pred A b} {f : Fin k → A} →
                ((d : Fin k) → ¬ (P (f d))) → All (∁ P) (tabulate f)
tabulate-none {zero} ¬p = []ₐ
tabulate-none {suc k} ¬p = (¬p 0F) ∷ₐ tabulate-none λ d → ¬p (fsuc d)

tabulate-∞ : (tabulate λ d → (d , ∞#)) † ≡ []
tabulate-∞ = filter-none isValid? (tabulate-none invalid-pair)

LemmaA₂-iter : ∀ {k} (f : Fin k → Fin n → Route) →
           ⨁ₛ (λ q → ((tabulate λ d → (d , f q d)) †)) ↭ (tabulate λ d → (d , (⨁ λ q → f q d))) †
LemmaA₂-iter {zero} f = ↭-reflexive (sym tabulate-∞)
LemmaA₂-iter {suc k} f = begin
  ⨁ₛ (λ q → ((tabulate λ d → (d , f q d)) †))                                                  ≡⟨⟩
  ((tabulate λ d → (d , f fzero d)) †) ⊕ₛ (⨁ₛ (λ q → ((tabulate λ d → (d , f (fsuc q) d)) †))) ↭⟨ ⊕ₛ-cong {(tabulate λ d → (d , f fzero d)) †} ↭-refl (LemmaA₂-iter (f ∘ fsuc)) ⟩
  ((tabulate λ d → (d , f fzero d)) †) ⊕ₛ ((tabulate λ d → (d , (⨁ (λ q → f (fsuc q) d)))) †)  ↭⟨ LemmaA₂ (f fzero) (λ d → ⨁ (λ q → f (fsuc q) d)) ⟩
  (tabulate λ d → (d , ((f fzero d) ⊕ (⨁ (λ q → f (fsuc q) d))))) †                            ≡⟨⟩
  (tabulate λ d → (d , (⨁ λ q → f q d))) † ∎
  where open PermutationReasoning

-- Lemma A.1
⊕-distributive : ∀ A B → ~(A ⊕ₘ B) ≈ᵥ (~ A) ⊕ᵥ (~ B)
⊕-distributive A B i = begin
  (~(A ⊕ₘ B)) i                                                        ≡⟨⟩
  (tabulate λ j → (j , (A i j) ⊕ (B i j))) †                           ↭⟨ ↭-sym (LemmaA₂ (λ j → A i j) (λ j → B i j)) ⟩
  ((tabulate (λ d → d , A i d)) †) ⊕ₛ ((tabulate (λ d → d , B i d)) †) ≡⟨⟩
  (~ A) i ⊕ₛ (~ B) i ∎
  where open PermutationReasoning

x=∞⇒fx=∞ : ∀ {v} {f : Route → Route} → v ≈ ∞# → f v ≈ ∞#
x=∞⇒fx=∞ {v} {f} v=∞ = ≈-trans (f-cong f v=∞) (f-fix f)

isValid-f : ∀ {d v} {f : Route → Route} → isValid (d , f v) → isValid (d , v)
isValid-f {d} {v} {f} = contraposition (x=∞⇒fx=∞ {v} {f})

isInvalid-f : ∀ {d v} {f : Route → Route} → ¬ (isValid (d , v)) → ¬ (isValid (d , f v))
isInvalid-f {d} {v} {f} = contraposition (isValid-f {d} {v} {f})

map-†-lemma : ∀ {xs f} → (map₂ f xs) † ↭ (map₂ f (xs †)) †
map-†-lemma {[]} {f} = ↭-refl
map-†-lemma {(d , v) ∷ xs} {f} with does (isValid? (d , v))
... | false = p
  where p : ((d , f v) ∷ (map₂ f xs)) † ↭ (map₂ f (xs †)) †
        p with does (isValid? (d , f v))
        ... | false = map-†-lemma {xs}
        ... | true = contradiction {!!} (isInvalid-f {d} {v} {f} {!!})
        -- need to use the proofs of isValid here, but doing a normal with-statement with "yes"\"no" does not allow for reduction
... | true = p
  where p : ((d , f v) ∷ (map₂ f xs)) † ↭ ((d , f v) ∷ (map₂ f (xs †))) †
        p with does (isValid? (d , f v))
        ... | false = map-†-lemma {xs}
        ... | true = prep ≈ᵣ-refl (map-†-lemma {xs})

map₂-map : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
           (xs : List (C × A)) (f : A → B) → map₂ f xs ≡ map (λ {(d , v) → (d , f v)}) xs
map₂-map [] f = refl
map₂-map ((d , v) ∷ xs) f = cong ((d , f v) ∷_) (map₂-map xs f)

map₂-tabulate : ∀ {a b c} {n} {A : Set a} {B : Set b} {C : Set c}
               (g : Fin n → C × A) (f : A → B) →
               map₂ f (tabulate g) ≡ tabulate ((λ {(d , v) → (d , f v)}) ∘ g)
map₂-tabulate g f = ≡ₗ-trans (map₂-map (tabulate g) f) (map-tabulate g (λ {(d , v) → (d , f v)}))
  where open import Relation.Binary.PropositionalEquality using () renaming (trans to ≡ₗ-trans)

~-lemma : ∀ {i q Y} → map₂ (λ v → (A i q) ▷ v) ((~ Y) q) † ↭  (tabulate λ d → (d , (A i q) ▷ (Y q d))) †
~-lemma {i} {q} {Y} = begin
  map₂ (λ v → (A i q) ▷ v) ((~ Y) q) †                                   ≡⟨⟩
  (map₂ ((A i q) ▷_) ((tabulate (λ d → (d , Y q d))) †)) †        ↭⟨ ↭-sym (map-†-lemma {(tabulate (λ d → (d , Y q d)))}) ⟩
  (map₂ ((A i q) ▷_) (tabulate (λ d → (d , Y q d))))     †        ↭⟨ †-cong (↭-reflexive (map₂-tabulate ((λ d → (d , Y q d))) ((A i q) ▷_))) ⟩
  (tabulate ((λ {(d , v) → (d , (A i q) ▷ v)}) ∘ (λ d → (d , Y q d)))) † ≡⟨⟩
  (tabulate λ d → (d , (A i q) ▷ (Y q d))) † ∎
  where open PermutationReasoning

-- Lemma 3.1
Lemma-Γ₀=Γ₁ : ∀ {Y} → A 〚 ~ Y 〛 ≈ᵥ ~ (A 〔 Y 〕)
Lemma-Γ₀=Γ₁ {Y} i = begin
  (A 〚 ~ Y 〛) i                                        ≡⟨⟩
  ⨁ₛ (λ q → (toRouteMap (A i q)) [ (~ Y) q ])           ≡⟨⟩
  ⨁ₛ (λ q → (λ s → (A i q) ▷ s) [ (~ Y) q ])            ≡⟨⟩  
  ⨁ₛ (λ q → (map₂ (λ v → (A i q) ▷ v) ((~ Y) q)) †)     ↭⟨ ⨁ₛ-cong (λ {q} → ~-lemma {i} {q} {Y}) ⟩
  ⨁ₛ (λ q → (tabulate λ d → (d , (A i q) ▷ (Y q d))) †) ↭⟨ LemmaA₂-iter (λ q d → (A i q) ▷ (Y q d)) ⟩
  (tabulate λ q → (q , ⨁ (λ k → (A i k) ▷ (Y k q)))) †  ≡⟨⟩
  (tabulate λ q → (q , (A 〔 Y 〕) i q)) †               ≡⟨⟩
  (~ (A 〔 Y 〕)) i ∎
  where open PermutationReasoning

-- Theorem 3
Γ₀=Γ₁ : {Y : RoutingMatrix} →
        Γ₁ (~ Y) ≈ᵥ ~ (Γ₀ Y)
Γ₀=Γ₁ {Y} = begin
  Γ₁ (~ Y)                ≡⟨⟩
  (A 〚 ~ Y 〛) ⊕ᵥ ~ M     ≈⟨ ⊕ᵥ-cong Lemma-Γ₀=Γ₁ (≈ₘ⇒≈ᵥ ≈ₘ-refl) ⟩
  (~ (A 〔 Y 〕)) ⊕ᵥ ~ M   ≈⟨ ≈ᵥ-sym (⊕-distributive (A 〔 Y 〕) M) ⟩
  ~ (A 〔 Y 〕 ⊕ₘ M)       ≡⟨⟩
  ~ (Γ₀ Y)                 ∎
  where open EqReasoning 𝕍ₛ

-- Theorem 2
FixedPoint-Γ₁ : ∀ {X} → IsFixedPoint _≈ₘ_ Γ₀ X → IsFixedPoint _≈ᵥ_ Γ₁ (~ X)
FixedPoint-Γ₁ {X} FP-Γ₀ = begin
  Γ₁ (~ X)           ≈⟨ Γ₀=Γ₁ ⟩
  ~ (Γ₀ X)           ≈⟨ ≈ₘ⇒≈ᵥ FP-Γ₀ ⟩
  ~ X                ∎
  where open EqReasoning 𝕍ₛ

-- Theorem 4
Γ₀=Γ₁-iter : ∀ {k Y} → (Γ₁ ^ k) (~ Y) ≈ᵥ ~ ((Γ₀ ^ k) Y) 
Γ₀=Γ₁-iter {zero} {Y}  = ≈ᵥ-refl
Γ₀=Γ₁-iter {suc k} {Y} = begin
  (Γ₁ ^ suc k) (~ Y)   ≡⟨⟩
  Γ₁ ((Γ₁ ^ k) (~ Y))  ≈⟨ Γ₁-cong (Γ₀=Γ₁-iter {k}) ⟩
  Γ₁ (~ ((Γ₀ ^ k) Y))  ≈⟨ Γ₀=Γ₁ ⟩
  ~ (Γ₀ ((Γ₀ ^ k) Y))  ≡⟨⟩
  ~ (Γ₀ ^ suc k) Y     ∎
  where open EqReasoning 𝕍ₛ
