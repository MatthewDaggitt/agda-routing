open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; _×_)
open import Data.List using (List; filter; tabulate)
open import Relation.Binary using (Setoid; Rel)
import Relation.Binary.EqReasoning as EqReasoning

open import RoutingLib.lmv34.Function using (_^_)
import RoutingLib.Data.List.Relation.Binary.Permutation.Setoid as PermutationEq
open import RoutingLib.Data.List.Relation.Binary.Permutation.Setoid.Properties
open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
open import RoutingLib.Routing as Routing using (AdjacencyMatrix)
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
open Routing algebra n
open Gamma_zero algebra A
open Gamma_zero_Algebra algebra n
open Gamma_one isRoutingAlgebra A
open Gamma_one_Algebra isRoutingAlgebra n

------------
open Setoid ↭-setoid
open Setoid ×-setoid renaming (_≈_ to _≈₁_)

tabulate-cong : ∀ {n} (f g : Fin n → {!!}) → ((k : Fin n) → ((f k) ≈₁ (g k))) → (tabulate f) ↭ (tabulate g)
tabulate-cong = {!!}

tab-M≈ : ∀ {i} {M M' : RoutingMatrix} → M ≈ₘ M' →
         (tabulate λ j → (j , M i j)) ↭ (tabulate λ j → (j , M' i j))
tab-M≈ {i} {M} {M'} M=M' = begin
  (tabulate λ j → (j , M i j)) ↭⟨ {!!} ⟩
  (tabulate λ j → (j , M' i j)) ∎
  where open PermutationReasoning

≈ₘ⇒≈ᵥ : ∀ {M M' : RoutingMatrix} → M ≈ₘ M' → ~ M ≈ᵥ ~ M'
(≈ₘ⇒≈ᵥ M=M') i = ↭-filter (tab-M≈ M=M')

≈ᵥ-cong : ∀ {V V'} → (f : RoutingVector → RoutingVector) → V ≈ᵥ V' → f V ≈ᵥ f V'
≈ᵥ-cong = {!!}

------------
-- Theorem 3
Γ₀=Γ₁ : {Y : RoutingMatrix} →
        Γ₁ (~ Y) ≈ᵥ ~ (Γ₀ Y)
Γ₀=Γ₁ {Y} i = begin
  ((Γ₁ (~ Y)) i) ↭⟨ {!!} ⟩
  (~ (A 〔 Y 〕 ⊕ₘ I)) i ↭⟨ ↭-refl ⟩
  ((~ Γ₀ Y) i) ∎
  where open PermutationReasoning

------------
-- Theorem 2
FixedPoint-Γ₁ : {X : RoutingMatrix} →
                (X ≈ₘ (A 〔 X 〕 ⊕ₘ I)) →
                ~ X ≈ᵥ (A 〚 ~ X 〛 ⊕ᵥ ~ I)
FixedPoint-Γ₁ {X} X=A[X]⊕I = begin
  ~ X                 ≈⟨ ≈ₘ⇒≈ᵥ X=A[X]⊕I ⟩
  ~ (A 〔 X 〕 ⊕ₘ I)  ≈⟨ ≈ₘ⇒≈ᵥ ≈ₘ-refl ⟩
  ~ (Γ₀ X)            ≈⟨ ≈ᵥ-sym Γ₀=Γ₁ ⟩
  Γ₁ (~ X)            ≈⟨ ≈ᵥ-refl ⟩
  A 〚 ~ X 〛 ⊕ᵥ ~ I  ∎
  where open EqReasoning 𝕍ₛ using (begin_ ; _∎; _≈⟨_⟩_)

------------
-- Theorem 4
Γ₀=Γ₁-iter : ∀ {k} {Y : RoutingMatrix} →
        (Γ₁ ^ k) (~ Y) ≈ᵥ ~ ((Γ₀ ^ k) Y) 
Γ₀=Γ₁-iter {zero} {Y}  = ≈ᵥ-refl
Γ₀=Γ₁-iter {suc k} {Y} = begin
  (Γ₁ ^ suc k) (~ Y)   ≈⟨ ≈ᵥ-refl ⟩
  Γ₁ ((Γ₁ ^ k) (~ Y))  ≈⟨ ≈ᵥ-cong Γ₁ (Γ₀=Γ₁-iter {k}) ⟩
  Γ₁ (~ ((Γ₀ ^ k) Y))  ≈⟨ Γ₀=Γ₁ ⟩
  ~ (Γ₀ ((Γ₀ ^ k) Y))  ≈⟨ ≈ᵥ-refl ⟩
  ~ (Γ₀ ^ suc k) Y     ∎
  where open EqReasoning 𝕍ₛ using (begin_ ; _∎; _≈⟨_⟩_)
