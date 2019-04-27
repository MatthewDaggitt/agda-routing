open import Algebra.FunctionProperties
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using () renaming (setoid to Fin-setoid)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; _×_)
open import Data.List using (List; []; _∷_; filter; tabulate; map)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (¬?; contradiction)
open import Relation.Unary using (Pred; Decidable)
open import Function using (_∘_)
open import Relation.Binary using (Setoid; DecSetoid; Rel)
import Relation.Binary.EqReasoning as EqReasoning

open import RoutingLib.lmv34.Function using (_^_)
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
open Routing algebra n renaming (I to M)
open Gamma_zero algebra A
open Gamma_zero_Algebra algebra n
open Gamma_one isRoutingAlgebra A
open Gamma_one_Algebra isRoutingAlgebra n

open Setoid (Fin-setoid n) using () renaming (refl to Fin-refl)
open DecSetoid FinRoute-decSetoid using () renaming (_≈_ to _≈ᵣ_; trans to ≈ᵣ-trans; sym to ≈ᵣ-sym)
open InsertionSort decTotalOrder using (sort)

------------------------------------
-- Operation properties

postulate
  ⊕ₛ-cong : Congruent₂ _↭_ _⊕ₛ_
  sort↭ : ∀ xs → sort xs ↭ xs
  Ø-identityᵣ : ∀ {A} → A ⊕ₛ Ø ↭ A

Ø-identityₗ : ∀ {A} → Ø ⊕ₛ A ↭ A
Ø-identityₗ {A} = sort↭ A
  
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

postulate
  †-cong : ∀ {A A' : RoutingSet} → A ↭ A' → A † ↭ A' †
  
{-†-cong : ∀ {A A' : RoutingSet} → A ↭ A' → A † ↭ A' †
†-cong {A} {.A} refl = refl
†-cong {A} {A'} (trans A=A' A'=A'') = trans (†-cong A=A') (†-cong A'=A'')
†-cong {(d , s) ∷ xs} {(d' , s') ∷ ys}
                (prep (d=d' , s=s') A=A')
                with ((s ≟ ∞#)) | ((s' ≟ ∞#))
... | yes p | no ¬p = contradiction (≈-trans (≈-sym s=s') p) ¬p
... | no ¬p | yes p = contradiction (≈-trans s=s' p) ¬p
... | yes _ | yes _ = †-cong A=A'
... | no _  | no _  = prep (d=d' , s=s') (†-cong A=A')
†-cong {((d₁ , s₁) ∷ (d₂ , s₂) ∷ xs)} {((d₂' , s₂') ∷ (d₁' , s₁') ∷ ys)}
                (swap (d₁=d₁' , s₁=s₁') (d₂=d₂' , s₂=s₂') A=A')
                with s₁ ≟ ∞# | s₁' ≟ ∞# | s₂ ≟ ∞# | s₂' ≟ ∞#
... | yes p | no ¬p | _     | _      = contradiction (≈-trans (≈-sym s₁=s₁') p) ¬p
... | no ¬p | yes p | _     | _      = contradiction (≈-trans s₁=s₁' p) ¬p
... | _     | _     | yes p | no ¬p  = contradiction (≈-trans (≈-sym s₂=s₂') p) ¬p
... | _     | _     | no ¬p | yes p  = contradiction (≈-trans s₂=s₂' p) ¬p
... | yes _ | yes _ | no _  | no _   = {!prep (d₂=d₂' , s₂=s₂') (†-cong A=A')!}
... | no _  | no _  | yes _ | yes _  = {!prep (d₂=d₂' , s₂=s₂') (†-cong A=A')!}
... | no _  | no _  | no _  | no _   = {!!}
... | yes _ | yes _ | yes _ | yes _  = {!!}-}

[]-cong : ∀ {i j} {f : Step i j} {A A'} →
          A ↭ A' → f [ A ] ↭ f [ A' ]
[]-cong A=A' = †-cong (lemma A=A')
  where lemma : {A A' : RoutingSet} → {i j : Fin n} → {f : Step i j} →
                A ↭ A' → map (λ {(d , v) → (d , f ▷ v)}) A ↭ map (λ {(d , v) → (d , f ▷ v)}) A'
        lemma refl = refl
        lemma (trans A=A'' A''=A') = trans (lemma A=A'') (lemma A''=A')
        lemma {f = f} (prep (d=d' , v=v') A=A') = prep (d=d' , ▷-cong f v=v') (lemma A=A')
        lemma {f = f} (swap (d₁=d₁' , v₁=v₁') (d₂=d₂' , v₂=v₂')  A=A') =
                swap ((d₁=d₁' , ▷-cong f v₁=v₁')) ((d₂=d₂' , ▷-cong f v₂=v₂')) (lemma A=A')

〚〛-cong : ∀ {V V'} → V ≈ᵥ V' → A 〚 V 〛 ≈ᵥ A 〚 V' 〛
〚〛-cong V=V' i = ⨁ₛ-cong (λ {q} → []-cong (V=V' q))

≈ₘ⇒≈ᵥ : ∀ {M M' : RoutingMatrix} → M ≈ₘ M' → ~ M ≈ᵥ ~ M'
(≈ₘ⇒≈ᵥ M=M') i = †-cong (lemma (λ {j} → (Fin-refl , M=M' i j)))
  where lemma : ∀ {k} → {f g : Fin k → Fin n × Route} →
                (∀ {i} → f i ≈ᵣ g i) → tabulate f ↭ tabulate g
        lemma {zero} {f} {g} f=g = refl
        lemma {suc k} {f} {g} f=g = prep f=g (lemma {k} f=g)

Γ₁-cong : ∀ {V V'} → V ≈ᵥ V' → Γ₁ V ≈ᵥ Γ₁ V'
Γ₁-cong V=V' = ⊕ᵥ-cong (〚〛-cong V=V') (≈ₘ⇒≈ᵥ ≈ₘ-refl)

------------------------------------
-- Theorems 

-- Lemma A.2
postulate
  LemmaA₂ : ∀ {k} (f : Fin k → Fin n → Route) →
            ⨁ₛ (λ q → ((tabulate λ d → (d , f q d)) †)) ↭ (tabulate λ d → (d , (⨁ λ q → f q d))) †

-- Lemma A.1
postulate
  distributive~⊕ : ∀ {A B} → (~ A) ⊕ᵥ (~ B) ≈ᵥ ~(A ⊕ₘ B)
  {-distributive~⊕ {A} {B} i = begin
    (~ A) i ⊕ₛ (~ B) i ↭⟨ ↭-refl ⟩
    (tabulate λ j → (j , A i j)) † ⊕ₛ (tabulate λ j → (j , B i j)) † ↭⟨ {!!} ⟩
    (tabulate λ j → (j , (A i j) ⊕ (B i j))) † ↭⟨ ↭-refl ⟩
    (tabulate λ j → (j , (A ⊕ₘ B) i j)) † ↭⟨ ↭-refl ⟩
    (~(A ⊕ₘ B)) i ∎
    where open PermutationReasoning-}

postulate
  lemma₄ : ∀ {i q Y} → map (λ {(d , v) → (d , (A i q) ▷ v)}) ((~ Y) q) † ↭  (tabulate λ d → (d , (A i q) ▷ (Y q d))) †

-- Lemma 3.1
Lemma-Γ₀=Γ₁ : ∀ {Y} → A 〚 ~ Y 〛 ≈ᵥ ~ (A 〔 Y 〕)
Lemma-Γ₀=Γ₁ {Y} i = begin
  (A 〚 ~ Y 〛) i                                                ↭⟨ ↭-refl ⟩
  ⨁ₛ (λ q → (A i q) [ (~ Y) q ])                                 ↭⟨ ↭-refl ⟩
  ⨁ₛ (λ q → (map (λ {(d , v) → (d , (A i q) ▷ v)}) ((~ Y) q)) †) ↭⟨ ⨁ₛ-cong (λ {q} → lemma₄ {i} {q} {Y}) ⟩
  ⨁ₛ (λ q → (tabulate λ d → (d , (A i q) ▷ (Y q d))) †)          ↭⟨ LemmaA₂ (λ q d → (A i q) ▷ (Y q d)) ⟩
  (tabulate λ q → (q , ⨁ (λ k → (A i k) ▷ (Y k q)))) † ↭⟨        ↭-refl ⟩
  (tabulate λ q → (q , (A 〔 Y 〕) i q)) †                       ↭⟨ ↭-refl ⟩
  (~ (A 〔 Y 〕)) i ∎
  where open PermutationReasoning

-- Theorem 3
Γ₀=Γ₁ : {Y : RoutingMatrix} →
        Γ₁ (~ Y) ≈ᵥ ~ (Γ₀ Y)
Γ₀=Γ₁ {Y} = begin
  Γ₁ (~ Y)                 ≈⟨ ≈ᵥ-refl ⟩
  (A 〚 ~ Y 〛) ⊕ᵥ ~ M     ≈⟨ ⊕ᵥ-cong Lemma-Γ₀=Γ₁ (≈ₘ⇒≈ᵥ ≈ₘ-refl) ⟩
  (~ (A 〔 Y 〕)) ⊕ᵥ ~ M   ≈⟨ distributive~⊕ ⟩
  ~ (A 〔 Y 〕 ⊕ₘ M)       ≈⟨ ≈ᵥ-refl ⟩
  ~ (Γ₀ Y)                 ∎
  where open EqReasoning 𝕍ₛ using (begin_; _∎; _≈⟨_⟩_)

-- Theorem 2
FixedPoint-Γ₁ : {X : RoutingMatrix} →
                X ≈ₘ (A 〔 X 〕 ⊕ₘ M) →
                ~ X ≈ᵥ (A 〚 ~ X 〛 ⊕ᵥ ~ M)
FixedPoint-Γ₁ {X} X=A[X]⊕M = begin
  ~ X                 ≈⟨ ≈ₘ⇒≈ᵥ X=A[X]⊕M ⟩
  ~ (A 〔 X 〕 ⊕ₘ M)  ≈⟨ ≈ₘ⇒≈ᵥ ≈ₘ-refl ⟩
  ~ (Γ₀ X)            ≈⟨ ≈ᵥ-sym Γ₀=Γ₁ ⟩
  Γ₁ (~ X)            ≈⟨ ≈ᵥ-refl ⟩
  A 〚 ~ X 〛 ⊕ᵥ ~ M  ∎
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
