{-# OPTIONS --allow-unsolved-metas #-}

open import Algebra.FunctionProperties
open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (decSetoid to Fin-decSetoid)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; _×_)
open import Data.List using (List; []; _∷_; filter; tabulate; map)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary using (Setoid; DecSetoid; Rel)
import Relation.Binary.EqReasoning as EqReasoning

open import RoutingLib.lmv34.Function using (_^_)
import RoutingLib.Data.List.Sorting.InsertionSort as InsertionSort
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

tab-M≈ : ∀ {i} {M M' : RoutingMatrix} → M ≈ₘ M' →
         (tabulate λ j → (j , M i j)) ↭ (tabulate λ j → (j , M' i j))
tab-M≈ {i} {M} {M'} M=M' = begin
  (tabulate λ j → (j , M i j)) ↭⟨ {!!} ⟩
  (tabulate λ j → (j , M' i j)) ∎
  where open PermutationReasoning

------------------------------------
-- Operation properties

≈ₘ⇒≈ᵥ : ∀ {M M' : RoutingMatrix} → M ≈ₘ M' → ~ M ≈ᵥ ~ M'
(≈ₘ⇒≈ᵥ M=M') i = ↭-filter (tab-M≈ M=M')

⊕ₛ-cong : Congruent₂ _↭_ _⊕ₛ_
⊕ₛ-cong {A} {A'} {B} {B'} A=A' B=B' = {!!}

Ø-identityₗ : ∀ {A} → Ø ⊕ₛ A ↭ A
Ø-identityₗ {A} = {!sort↭ A!}

Ø-identityᵣ : ∀ {A} → A ⊕ₛ Ø ↭ A
Ø-identityᵣ {A} = {!sort↭ A!}

⨁ₛ-cong : ∀ {k} → {f g : Fin k → RoutingSet} →
          (∀ {i} → f i ↭ g i) → ⨁ₛ f ↭ ⨁ₛ g
⨁ₛ-cong {zero} {f} {g} f=g = ↭-refl
⨁ₛ-cong {suc k} {f} {g} f=g = ⊕ₛ-cong f=g (⨁ₛ-cong {k} f=g)

⊕ᵥ-cong : Congruent₂ _≈ᵥ_ _⊕ᵥ_
⊕ᵥ-cong V=V' W=W' i = ⊕ₛ-cong (V=V' i) (W=W' i)

Øᵥ-identityₗ : ∀ {A} → Øᵥ ⊕ᵥ A ≈ᵥ A
Øᵥ-identityₗ i = Ø-identityₗ

Øᵥ-identityᵣ : ∀ {A} → A ⊕ᵥ Øᵥ ≈ᵥ A
Øᵥ-identityᵣ i = Ø-identityᵣ

private
  lemma₁ : {A A' : RoutingSet} → {i j : Fin n} → {f : Step i j} →
           A ↭ A' → map (λ {(d , v) → (d , f ▷ v)}) A ↭ map (λ {(d , v) → (d , f ▷ v)}) A'
  lemma₁ refl = refl
  lemma₁ (trans A=A'' A''=A') = trans (lemma₁ A=A'') (lemma₁ A''=A')
  lemma₁ {f = f} (prep (d=d' , v=v') A=A') = prep (d=d' , ▷-cong f v=v') (lemma₁ A=A')
  lemma₁ {f = f} (swap (d₁=d₁' , v₁=v₁') (d₂=d₂' , v₂=v₂')  A=A') =
    swap ((d₁=d₁' , ▷-cong f v₁=v₁')) ((d₂=d₂' , ▷-cong f v₂=v₂')) (lemma₁ A=A')

†-cong : ∀ {A A' : RoutingSet} →
         A ↭ A' → A † ↭ A' †
†-cong refl = refl
†-cong (trans A=A'' A''=A') = trans (†-cong A=A'') (†-cong A''=A')
†-cong {.((d , v) ∷ A)} {.((d' , v') ∷ A')} (prep {A} {A'} {(d , v)} {(d' , v')} (d=d' , v=v') A=A') = {!!}
†-cong {.(_ ∷ _ ∷ _)} {.(_ ∷ _ ∷ _)} (swap eq₁ eq₂ A=A') = {!!}

[]-cong : ∀ {i j} {f : Step i j} {A A'} →
          A ↭ A' → f [ A ] ↭ f [ A' ]
[]-cong A=A' = †-cong (lemma₁ A=A')

〚〛-cong : ∀ {V V'} → V ≈ᵥ V' → A 〚 V 〛 ≈ᵥ A 〚 V' 〛
〚〛-cong V=V' i = ⨁ₛ-cong (λ {q} → []-cong (V=V' q))

Γ₁-cong : ∀ {V V'} → V ≈ᵥ V' → Γ₁ V ≈ᵥ Γ₁ V'
Γ₁-cong V=V' = ⊕ᵥ-cong (〚〛-cong V=V') (≈ₘ⇒≈ᵥ ≈ₘ-refl)

------------------------------------
-- Theorems 

-- Lemma A.1
distributive~⊕ : ∀ {A B} → (~ A) ⊕ᵥ (~ B) ≈ᵥ ~(A ⊕ₘ B)
distributive~⊕ {A} {B} = {!!}

-- Lemma 3.1
Lemma-Γ₀=Γ₁ : ∀ {Y} → A 〚 ~ Y 〛 ≈ᵥ ~ (A 〔 Y 〕)
Lemma-Γ₀=Γ₁ {Y} i = begin
  (A 〚 ~ Y 〛) i                ↭⟨ ↭-refl ⟩
  ⨁ₛ (λ q → (A i q) [ (~ Y) q ]) ↭⟨ ↭-refl ⟩
  ⨁ₛ (λ q → (map (λ {(d , v) → (d , (A i q) ▷ v)}) ((~ Y) q)) †) ↭⟨ ↭-refl ⟩
  ⨁ₛ (λ q → (map (λ {(d , v) → (d , (A i q) ▷ v)}) ((tabulate λ j → (j , Y q j)) †)) †) ↭⟨ {!!} ⟩ 
  (tabulate λ q → (q , ⨁ (λ k → (A i k) ▷ (Y k q)))) † ↭⟨ ↭-refl ⟩
  (tabulate λ q → (q , (A 〔 Y 〕) i q)) † ↭⟨ ↭-refl ⟩
  (~ (A 〔 Y 〕)) i                 ∎
  where open PermutationReasoning

-- Theorem 3
Γ₀=Γ₁ : {Y : RoutingMatrix} →
        Γ₁ (~ Y) ≈ᵥ ~ (Γ₀ Y)
Γ₀=Γ₁ {Y} = begin
  Γ₁ (~ Y)                 ≈⟨ ≈ᵥ-refl ⟩
  (A 〚 ~ Y 〛) ⊕ᵥ ~ I   ≈⟨ ⊕ᵥ-cong Lemma-Γ₀=Γ₁ (≈ₘ⇒≈ᵥ ≈ₘ-refl) ⟩
  (~ (A 〔 Y 〕)) ⊕ᵥ ~ I ≈⟨ distributive~⊕ ⟩
  ~ (A 〔 Y 〕 ⊕ₘ I)       ≈⟨ ≈ᵥ-refl ⟩
  ~ (Γ₀ Y)                 ∎
  where open EqReasoning 𝕍ₛ using (begin_; _∎; _≈⟨_⟩_)

-- Theorem 2
FixedPoint-Γ₁ : {X : RoutingMatrix} →
                X ≈ₘ (A 〔 X 〕 ⊕ₘ I) →
                ~ X ≈ᵥ (A 〚 ~ X 〛 ⊕ᵥ ~ I)
FixedPoint-Γ₁ {X} X=A[X]⊕I = begin
  ~ X                 ≈⟨ ≈ₘ⇒≈ᵥ X=A[X]⊕I ⟩
  ~ (A 〔 X 〕 ⊕ₘ I)  ≈⟨ ≈ₘ⇒≈ᵥ ≈ₘ-refl ⟩
  ~ (Γ₀ X)            ≈⟨ ≈ᵥ-sym Γ₀=Γ₁ ⟩
  Γ₁ (~ X)            ≈⟨ ≈ᵥ-refl ⟩
  A 〚 ~ X 〛 ⊕ᵥ ~ I  ∎
  where open EqReasoning 𝕍ₛ using (begin_ ; _∎; _≈⟨_⟩_)

-- Theorem 4
Γ₀=Γ₁-iter : ∀ {k Y} → (Γ₁ ^ k) (~ Y) ≈ᵥ ~ ((Γ₀ ^ k) Y) 
Γ₀=Γ₁-iter {zero} {Y}  = ≈ᵥ-refl
Γ₀=Γ₁-iter {suc k} {Y} = begin
  (Γ₁ ^ suc k) (~ Y)   ≈⟨ ≈ᵥ-refl ⟩
  Γ₁ ((Γ₁ ^ k) (~ Y))  ≈⟨ Γ₁-cong (Γ₀=Γ₁-iter {k}) ⟩
  Γ₁ (~ ((Γ₀ ^ k) Y))  ≈⟨ Γ₀=Γ₁ ⟩
  ~ (Γ₀ ((Γ₀ ^ k) Y))  ≈⟨ ≈ᵥ-refl ⟩
  ~ (Γ₀ ^ suc k) Y     ∎
  where open EqReasoning 𝕍ₛ using (begin_ ; _∎; _≈⟨_⟩_)
