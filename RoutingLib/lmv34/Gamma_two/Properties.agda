open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_,_; _×_)
open import Data.Product.Relation.Pointwise.NonDependent using (_×ₛ_)
open import Function using (_∘_)
open import Level using (_⊔_)
open import Data.List using (List; filter; tabulate; [])
open import Data.Nat using (zero; suc; ℕ; _*_; _+_)
open import Relation.Binary using (Setoid; Rel; Reflexive; Symmetric; Transitive; _⇒_)
import Relation.Binary.EqReasoning as EqReasoning

open import RoutingLib.lmv34.Function using (_^_)
open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
open import RoutingLib.Routing as Routing using () renaming (AdjacencyMatrix to AdjacencyMatrix₁)
import RoutingLib.lmv34.Gamma_zero as Gamma_zero
import RoutingLib.lmv34.Gamma_zero.Algebra as Gamma_zero_Algebra
import RoutingLib.lmv34.Gamma_one as Gamma_one
import RoutingLib.lmv34.Gamma_one.Algebra as Gamma_one_Algebra
import RoutingLib.lmv34.Gamma_one.Properties as Gamma_one_Properties
import RoutingLib.lmv34.Gamma_two as Gamma_two
open import RoutingLib.lmv34.Gamma_two.Algebra as Gamma_two_Algebra using (IsComposition; AdjacencyMatrixᵀ)

module RoutingLib.lmv34.Gamma_two.Properties
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra) {n}
  (A    : AdjacencyMatrix₁ algebra n)
  (ImpProt : AdjacencyMatrix₁ algebra n)
  (Exp  : AdjacencyMatrixᵀ isRoutingAlgebra n)
  (A=Imp∘Prot∘Exp : IsComposition isRoutingAlgebra n A ImpProt Exp)
  where

open RawRoutingAlgebra algebra
open Routing algebra n renaming (I to M) using (RoutingMatrix; _≈ₘ_; ≈ₘ-refl)
open Gamma_zero algebra A
open Gamma_zero_Algebra algebra n
open Gamma_one isRoutingAlgebra A
open Gamma_one_Algebra isRoutingAlgebra n
open Gamma_one_Properties isRoutingAlgebra A
open Gamma_two isRoutingAlgebra ImpProt Exp
open Gamma_two_Algebra isRoutingAlgebra n

-- Γ₂-State setoid
infix 2 _≈ₛ_

_≈ₛ_ : Rel Γ₂-State (a ⊔ ℓ)
S ≈ₛ S' = Γ₂-State.V S ≈ᵥ   Γ₂-State.V S' ×
          Γ₂-State.I S ≈ᵥ,₂ Γ₂-State.I S' ×
          Γ₂-State.O S ≈ᵥ,₂ Γ₂-State.O S'

≈ₛ-refl : Reflexive _≈ₛ_
≈ₛ-refl = (≈ᵥ-refl , ≈ᵥ,₂-refl , ≈ᵥ,₂-refl)
≈ₛ-sym : Symmetric _≈ₛ_
≈ₛ-sym (V=V' , I=I' , O=O') = (≈ᵥ-sym V=V' , ≈ᵥ,₂-sym I=I' , ≈ᵥ,₂-sym O=O')
≈ₛ-trans : Transitive _≈ₛ_
≈ₛ-trans (V=V' , I=I' , O=O') (V'=V'' , I'=I'' , O'=O'') =
  (≈ᵥ-trans V=V' V'=V'' , ≈ᵥ,₂-trans I=I' I'=I'' , ≈ᵥ,₂-trans O=O' O'=O'')
  
𝕊ₛ : Setoid a (a ⊔ ℓ)
𝕊ₛ = record {Carrier = Γ₂-State;
             _≈_ = _≈ₛ_;
             isEquivalence =
               record {refl = ≈ₛ-refl; sym = ≈ₛ-sym; trans = ≈ₛ-trans}}

------------------------------------
-- Operation properties

【】-cong : ∀ {F V V'} → V ≈ᵥ V' → (F 【 V 】) ≈ᵥ,₂ (F 【 V' 】)
【】-cong V=V' i j = []-cong (V=V' i)

〖〗-cong : ∀ {F O O'} → O ≈ᵥ,₂ O' → (F 〖 O 〗) ≈ᵥ,₂ (F 〖 O' 〗)
〖〗-cong O=O' i j = []-cong (O=O' j i)

↓-cong : ∀ {I I'} → I ≈ᵥ,₂ I' → I ↓ ≈ᵥ I' ↓
↓-cong I=I' i = ⨁ₛ-cong (λ {q} → I=I' i q)

private
  lemma : ∀ {k} → ⨁ₛ (λ (q : Fin k) → []) ↭ []
  lemma {zero} = ↭-refl
  lemma {suc k} = ↭-trans Ø-identityₗ (lemma {k})

Øᵥ,₂↓=Øᵥ : Øᵥ,₂ ↓ ≈ᵥ Øᵥ
Øᵥ,₂↓=Øᵥ i = lemma {n}

Γ₂,ᵥ-cong : ∀ {I I'} → I ≈ᵥ,₂ I' → Γ₂,ᵥ I ≈ᵥ Γ₂,ᵥ I'
Γ₂,ᵥ-cong {I} {I'} I=I' = ⊕ᵥ-cong (↓-cong I=I') (≈ₘ⇒≈ᵥ ≈ₘ-refl)

Γ₂,ᵢ-cong : ∀ {O O'} → O ≈ᵥ,₂ O' → Γ₂,ᵢ O ≈ᵥ,₂ Γ₂,ᵢ O'
Γ₂,ᵢ-cong = 〖〗-cong

Γ₂,ₒ-cong : ∀ {V V'} → V ≈ᵥ V' → Γ₂,ₒ V ≈ᵥ,₂ Γ₂,ₒ V'
Γ₂,ₒ-cong = 【】-cong

Γ₂-cong : ∀ {S S'} → S ≈ₛ S' → Γ₂-Model S ≈ₛ Γ₂-Model S'
Γ₂-cong (V=V' , I=I' , O=O') = Γ₂,ᵥ-cong I=I' , Γ₂,ᵢ-cong O=O' , Γ₂,ₒ-cong V=V'

Γ₂-iter-cong : ∀ {k S S'} → S ≈ₛ S' → (Γ₂-Model ^ k) S ≈ₛ (Γ₂-Model ^ k) S'
Γ₂-iter-cong {zero} S=S' = S=S'
Γ₂-iter-cong {suc k} S=S' = Γ₂-cong (Γ₂-iter-cong {k} S=S')

------------------------------------
-- Theorems

-- Lemma A.4


-- Lemma 3.2
Γ₁=Γ₂,ᵥ : ∀ {k} {X : RoutingMatrix} →
          (Γ₁ ^ (suc k)) (~ X) ≈ᵥ (Γ₂,ᵥ ∘ Γ₂,ᵢ ∘ Γ₂,ₒ) ((Γ₁ ^ k) (~ X))
Γ₁=Γ₂,ᵥ {k} {X} = begin
        (Γ₁ ^ (suc k)) (~ X) ≈⟨ ≈ᵥ-refl ⟩
        Γ₁ ((Γ₁ ^ k) (~ X)) ≈⟨ ≈ᵥ-refl ⟩
        A 〚 (Γ₁ ^ k) (~ X)  〛 ⊕ᵥ ~ M ≈⟨ {!!} ⟩
        (ImpProt 〖 Exp 【 (Γ₁ ^ k) (~ X) 】 〗) ↓ ⊕ᵥ ~ M ≈⟨ ≈ᵥ-refl ⟩
        (ImpProt 〖 Γ₂,ₒ ((Γ₁ ^ k) (~ X))  〗) ↓ ⊕ᵥ ~ M ≈⟨ ≈ᵥ-refl ⟩
        (Γ₂,ᵥ ∘ Γ₂,ᵢ ∘ Γ₂,ₒ) ((Γ₁ ^ k) (~ X)) ∎
        where open EqReasoning 𝕍ₛ using (begin_; _∎; _≈⟨_⟩_)

-- Theorem 5
FixedPoint-Γ₂ : ∀ {V I O} →
                Γ₂-Model (record {V = V; I = I; O = O}) ≈ₛ record {V = V; I = I; O = O} →
                (V ≈ᵥ I ↓ ⊕ᵥ ~ M) ×
                (I ≈ᵥ,₂ (ImpProt 〖 O 〗)) ×
                (O ≈ᵥ,₂ (Exp 【 V 】))
FixedPoint-Γ₂ {V} {I} {O} (V=V , I=I , O=O) =
        ≈ᵥ-sym V=V ,
        ≈ᵥ,₂-sym I=I ,
        ≈ᵥ,₂-sym O=O

-- Theorem 6
FixedPoint-Γ₀-Γ₂ : ∀ {X : RoutingMatrix} →
                   X ≈ₘ (A 〔 X 〕 ⊕ₘ M) →
                   ((~ X) ≈ᵥ (ImpProt 〖 Exp 【 ~ X 】 〗) ↓ ⊕ᵥ ~ M) ×
                   ((ImpProt 〖 Exp 【 ~ X 】 〗) ≈ᵥ,₂ (ImpProt 〖 Exp 【 ~ X 】 〗)) ×
                   ((Exp 【 ~ X 】) ≈ᵥ,₂ (Exp 【 ~ X 】))
FixedPoint-Γ₀-Γ₂ {X} X=AX⊕M  =
        (begin
            ~ X                 ≈⟨ ≈ₘ⇒≈ᵥ X=AX⊕M ⟩
            ~ (A 〔 X 〕 ⊕ₘ M)  ≈⟨ ≈ₘ⇒≈ᵥ ≈ₘ-refl ⟩
            ~ (Γ₀ X)            ≈⟨ ≈ᵥ-sym Γ₀=Γ₁ ⟩
            Γ₁ (~ X)            ≈⟨ Γ₁=Γ₂,ᵥ {zero} ⟩
            Γ₂,ᵥ I              ≈⟨ ≈ᵥ-refl ⟩
            I ↓ ⊕ᵥ ~ M ∎) ,
        ≈ᵥ,₂-refl ,
        ≈ᵥ,₂-refl
        where
          open EqReasoning 𝕍ₛ using (begin_ ; _∎; _≈⟨_⟩_)
          I = ImpProt 〖 Exp 【 ~ X 】 〗
-- Use where here for V, I, O in type signature if possible

Lemma1 : ∀ {A : RoutingMatrix} → Γ₂,ₒ (Øᵥ,₂ ↓ ⊕ᵥ ~ A) ≈ᵥ,₂ Γ₂,ₒ (~ A)
Lemma1 {A} = Γ₂,ₒ-cong (≈ᵥ-trans (⊕ᵥ-cong Øᵥ,₂↓=Øᵥ (≈ₘ⇒≈ᵥ ≈ₘ-refl))
                                 (Øᵥ-identityₗ {~ A}))
Lemma2 : ∀ {A} → (Γ₂,ᵢ ∘ Γ₂,ₒ) (Øᵥ,₂ ↓ ⊕ᵥ ~ A) ≈ᵥ,₂ (Γ₂,ᵢ ∘ Γ₂,ₒ) (~ A)
Lemma2 = Γ₂,ᵢ-cong Lemma1

-- Theorem 7
Γ₁=Γ₂ : ∀ {k} →
        (Γ₂-Model ^ (3 * (suc k)))
          (record {V = ~ M;
                   I = Øᵥ,₂;
                   O = Øᵥ,₂}) ≈ₛ
        (record   {V = (Γ₁ ^ (suc k)) (~ M);
                   I = (Γ₂,ᵢ ∘ Γ₂,ₒ) ((Γ₁ ^ k) (~ M));
                   O = Γ₂,ₒ ((Γ₁ ^ k) (~ M))})
Γ₁=Γ₂ {zero} = begin
        (Γ₂-Model ^ 3) (record {V = ~ M; I = Øᵥ,₂; O = Øᵥ,₂})
          ≈⟨ ≈ₛ-refl ⟩
        record { V = (Γ₂,ᵥ ∘ Γ₂,ᵢ ∘ Γ₂,ₒ) (~ M);
                 I = (Γ₂,ᵢ ∘ Γ₂,ₒ) (Øᵥ,₂ ↓ ⊕ᵥ ~ M);
                 O = Γ₂,ₒ (Øᵥ,₂ ↓ ⊕ᵥ ~ M)}
          ≈⟨ ≈ᵥ-sym (Γ₁=Γ₂,ᵥ {zero} {M}) , Lemma2 , Lemma1 ⟩
        record {V = Γ₁ (~ M);
                 I = (Γ₂,ᵢ ∘ Γ₂,ₒ) (~ M);
                 O = Γ₂,ₒ (~ M)} ∎
        where open EqReasoning 𝕊ₛ
Γ₁=Γ₂ {suc k} = begin
        (Γ₂-Model ^ (3 * suc (suc k)))
        (record {V = ~ M;
                 I = Øᵥ,₂;
                 O = Øᵥ,₂})
          ≈⟨ {!!} ⟩
        (Γ₂-Model ^ 3) ((Γ₂-Model ^ (3 * (suc k)))
        (record {V = ~ M;
                 I = Øᵥ,₂;
                 O = Øᵥ,₂}))
          ≈⟨ Γ₂-iter-cong {3} (Γ₁=Γ₂ {k}) ⟩
        (Γ₂-Model ^ 3)
        (record {V = (Γ₁ ^ (suc k)) (~ M);
                 I = (Γ₂,ᵢ ∘ Γ₂,ₒ) ((Γ₁ ^ k) (~ M));
                 O = Γ₂,ₒ ((Γ₁ ^ k) (~ M))})
          ≈⟨ Γ₂-iter-cong {2}
                 {Γ₂-Model (record {V = (Γ₁ ^ (suc k)) (~ M);
                                    I = (Γ₂,ᵢ ∘ Γ₂,ₒ) ((Γ₁ ^ k) (~ M));
                                    O = Γ₂,ₒ ((Γ₁ ^ k) (~ M))})}
                 {(record {         V = (Γ₁ ^ (suc k)) (~ M);
                                    I = (Γ₂,ᵢ ∘ Γ₂,ₒ) ((Γ₁ ^ k) (~ M));
                                    O = Γ₂,ₒ ((Γ₁ ^ (suc k)) (~ M))})}
                 (≈ᵥ-sym (Γ₁=Γ₂,ᵥ {k} {M}) , ≈ᵥ,₂-refl {n} {n} , ≈ᵥ,₂-refl {n} {n}) ⟩
        (Γ₂-Model ^ 2)
        (record {V = (Γ₁ ^ (suc k)) (~ M);
                 I = (Γ₂,ᵢ ∘ Γ₂,ₒ) ((Γ₁ ^ k) (~ M));
                 O = Γ₂,ₒ ((Γ₁ ^ (suc k)) (~ M))})
          ≈⟨ Γ₂-iter-cong {1}
                 {Γ₂-Model (record {V = (Γ₁ ^ (suc k)) (~ M);
                                    I = (Γ₂,ᵢ ∘ Γ₂,ₒ) ((Γ₁ ^ k) (~ M));
                                    O = Γ₂,ₒ ((Γ₁ ^ (suc k)) (~ M))})}
                 {(record {         V = (Γ₁ ^ (suc k)) (~ M);
                                    I = (Γ₂,ᵢ ∘ Γ₂,ₒ) ((Γ₁ ^ (suc k)) (~ M));
                                    O = Γ₂,ₒ ((Γ₁ ^ (suc k)) (~ M))})}
                 (≈ᵥ-sym (Γ₁=Γ₂,ᵥ {k} {M}) , ≈ᵥ,₂-refl , ≈ᵥ,₂-refl) ⟩
        Γ₂-Model
        (record {V = (Γ₁ ^ (suc k)) (~ M);
                 I = (Γ₂,ᵢ ∘ Γ₂,ₒ) ((Γ₁ ^ (suc k)) (~ M));
                 O = Γ₂,ₒ ((Γ₁ ^ (suc k)) (~ M))})
          ≈⟨ ≈ᵥ-sym (Γ₁=Γ₂,ᵥ {suc k} {M}) , ≈ᵥ,₂-refl , ≈ᵥ,₂-refl ⟩
        record { V = (Γ₁ ^ suc (suc k)) (~ M);
                 I = (Γ₂,ᵢ ∘ Γ₂,ₒ) ((Γ₁ ^ suc k) (~ M));
                 O = Γ₂,ₒ ((Γ₁ ^ suc k) (~ M))} ∎
        where open EqReasoning 𝕊ₛ
