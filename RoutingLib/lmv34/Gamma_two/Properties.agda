open import Algebra.FunctionProperties.Core using (Op₂)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_,_; _×_)
open import Data.Product.Relation.Pointwise.NonDependent using (_×ₛ_)
open import Function using (_∘_)
open import Level using (_⊔_)
open import Data.List using (List; filter; tabulate; []; _∷_; map)
open import Data.Nat using (zero; suc; ℕ; _*_; _+_)
open import Data.Nat.Properties using (*-comm)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary using (Setoid; DecSetoid; Rel; Reflexive; Symmetric; Transitive; _⇒_)
open import Relation.Binary.PropositionalEquality as PropositionalEq using (_≡_; refl; cong)
import Relation.Binary.EqReasoning as EqReasoning

open import RoutingLib.lmv34.Function using (_^_)
open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
open import RoutingLib.Routing as Routing using () renaming (AdjacencyMatrix to AdjacencyMatrix')
import RoutingLib.lmv34.Gamma_zero as Gamma_zero
import RoutingLib.lmv34.Gamma_zero.Algebra as Gamma_zero_Algebra
import RoutingLib.lmv34.Gamma_one as Gamma_one
import RoutingLib.lmv34.Gamma_one.Algebra as Gamma_one_Algebra
import RoutingLib.lmv34.Gamma_one.Properties as Gamma_one_Properties
import RoutingLib.lmv34.Gamma_two as Gamma_two
open import RoutingLib.lmv34.Gamma_two.Algebra as Gamma_two_Algebra using (IsComposition; AdjacencyMatrixᵀ)

module RoutingLib.lmv34.Gamma_two.Properties
  {a b ℓ} {alg : RawRoutingAlgebra a b ℓ}
  (isRAlg : IsRoutingAlgebra alg) {n}
  (_●_ : ∀ {i j : Fin n} → Op₂ (RawRoutingAlgebra.Step alg i j))
  (A    : AdjacencyMatrix' alg n)
  (Imp Prot : AdjacencyMatrix' alg n)
  (Exp  : AdjacencyMatrixᵀ isRAlg n _●_)
  (A=Imp∘Prot∘Exp : IsComposition isRAlg n _●_ A Imp Prot Exp)
  where

open RawRoutingAlgebra alg
open Routing alg n renaming (I to M) using (RoutingMatrix; _≈ₘ_; ≈ₘ-refl)
open Gamma_zero alg A
open Gamma_zero_Algebra alg n
open Gamma_one isRAlg A
open Gamma_one_Algebra isRAlg n
open Gamma_one_Properties isRAlg A
open Gamma_two isRAlg _●_ Imp Prot Exp
open Gamma_two_Algebra isRAlg n _●_

open DecSetoid FinRoute-decSetoid using () renaming (_≈_ to _≈ᵣ_)

------------------------------------
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

f[]-cong : ∀ {i j} → {f f' : Step i j} → {X : RoutingSet} →
           f ≈ₐ f' → f [ X ] ↭ f' [ X ]
f[]-cong {i} {j} {f} {f'} {X} f=f' = †-cong (lemma {xs = X} λ {(d , v) → (refl , f=f' v)})
  where lemma : {f g : Fin n × Route → Fin n × Route} → {xs : RoutingSet} →
                (∀ r → f r ≈ᵣ g r) → map f xs ↭ map g xs
        lemma {f} {g} {[]} f=g = ↭-refl
        lemma {f} {g} {x ∷ xs} f=g = prep (f=g x) (lemma {xs = xs} f=g)

A〚〛-cong : ∀ {F F' V} → F ≈ₐ,₂ F' → F 〚 V 〛 ≈ᵥ  F' 〚 V 〛
A〚〛-cong {F} {F'} {V} F=F' i = ⨁ₛ-cong (λ {q} → f[]-cong {X = V q} (F=F' i q))

↓-cong : ∀ {I I'} → I ≈ᵥ,₂ I' → I ↓ ≈ᵥ I' ↓
↓-cong I=I' i = ⨁ₛ-cong (λ {q} → I=I' i q)

Øᵥ,₂↓=Øᵥ : Øᵥ,₂ ↓ ≈ᵥ Øᵥ
Øᵥ,₂↓=Øᵥ i = lemma {n}
  where lemma : ∀ {k} → ⨁ₛ (λ (q : Fin k) → []) ↭ []
        lemma {zero} = ↭-refl
        lemma {suc k} = ↭-trans Ø-identityₗ (lemma {k})

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


-- Theorem 5
FixedPoint-Γ₂ : ∀ {V I O} →
                Γ₂-Model (S₂ V I O) ≈ₛ S₂ V I O →
                (V ≈ᵥ I ↓ ⊕ᵥ ~ M) ×
                (I ≈ᵥ,₂ ((Imp ●ₘ Prot) 〖 O 〗)) ×
                (O ≈ᵥ,₂ (Exp 【 V 】))
FixedPoint-Γ₂ (V=V , I=I , O=O) =
        ≈ᵥ-sym V=V ,
        ≈ᵥ,₂-sym I=I ,
        ≈ᵥ,₂-sym O=O


-- Lemma A.3
postulate
  LemmaA₃ : ∀ {i j} → {f g : Step i j} → (X : RoutingSet) →
            f [ g [ X ] ] ↭ (f ● g) [ X ]
            
-- tgg: something wrong here, we don't have access to the meaning of _●_
-- LemmaA₃ {i} {j} {f} {g} X = 
--   begin
--   (f [ g [ X ] ])  ↭⟨ {!!} ⟩
--   ((f ● g) [ X ])  ∎       
--   where open PermutationReasoning  

-- Lemma A.4
LemmaA₄ : ∀ {F G V} → (F 〖 G 【 V 】 〗) ↓ ≈ᵥ (F ●ₘ (G ᵀ)) 〚 V 〛
LemmaA₄ {F} {G} {V} i = begin
  ((F 〖 G 【 V 】 〗) ↓) i ↭⟨ ↭-refl ⟩
  ⨁ₛ (λ q → (F i q) [ (G q i) [ V q ] ]) ↭⟨ ⨁ₛ-cong (λ {q} → (LemmaA₃ {f = F i q} {g = G q i} (V q))) ⟩
  ⨁ₛ (λ q → ((F i q) ● (G q i)) [ V q ]) ↭⟨ ↭-refl ⟩
  ((F ●ₘ (G ᵀ)) 〚 V 〛) i ∎
  where open PermutationReasoning

-- Lemma 3.2
-- Γ₁=Γ₂,ᵥ : ∀ {k} {X : RoutingMatrix} →
--           (Γ₁ ^ (suc k)) (~ X) ≈ᵥ (Γ₂,ᵥ ∘ Γ₂,ᵢ ∘ Γ₂,ₒ) ((Γ₁ ^ k) (~ X))
-- Γ₁=Γ₂,ᵥ {k} {X} = begin
--         (Γ₁ ^ (suc k)) (~ X) ≈⟨ ≈ᵥ-refl ⟩
--         A 〚 (Γ₁ ^ k) (~ X) 〛 ⊕ᵥ ~ M
--           ≈⟨ ⊕ᵥ-cong (A〚〛-cong {V = (Γ₁ ^ k) (~ X)} A=Imp∘Prot∘Exp) (≈ₘ⇒≈ᵥ ≈ₘ-refl) ⟩
--         ((Imp ●ₘ Prot) ●ₘ (Exp ᵀ)) 〚 (Γ₁ ^ k) (~ X) 〛 ⊕ᵥ ~ M
--           ≈⟨ ⊕ᵥ-cong (≈ᵥ-sym (LemmaA₄ {Imp ●ₘ Prot} {Exp} {V = (Γ₁ ^ k) (~ X)})) (≈ₘ⇒≈ᵥ ≈ₘ-refl) ⟩
--         ((Imp ●ₘ Prot) 〖 Exp 【 (Γ₁ ^ k) (~ X) 】 〗) ↓ ⊕ᵥ ~ M ≈⟨ ≈ᵥ-refl ⟩
--         (Γ₂,ᵥ ∘ Γ₂,ᵢ ∘ Γ₂,ₒ) ((Γ₁ ^ k) (~ X)) ∎
--         where open EqReasoning 𝕍ₛ using (begin_; _∎; _≈⟨_⟩_)


-- tgg : this is really the core of Γ₁=Γ₂,ᵥ : 
Γ₁=Γ₂,ᵥ : ∀ (V : RoutingVector) → Γ₁ V ≈ᵥ (Γ₂,ᵥ ∘ Γ₂,ᵢ ∘ Γ₂,ₒ) V 
Γ₁=Γ₂,ᵥ V = begin 
        Γ₁ V                                          ≈⟨ ≈ᵥ-refl ⟩
        A 〚 V 〛 ⊕ᵥ ~ M                              ≈⟨ ⊕ᵥ-cong (A〚〛-cong { V = V } A=Imp∘Prot∘Exp) (≈ₘ⇒≈ᵥ ≈ₘ-refl)  ⟩ 
        ((Imp ●ₘ Prot) ●ₘ (Exp ᵀ)) 〚 V 〛 ⊕ᵥ ~ M    ≈⟨ ⊕ᵥ-cong (≈ᵥ-sym (LemmaA₄ {Imp ●ₘ Prot} {Exp} { V = V })) (≈ₘ⇒≈ᵥ ≈ₘ-refl)   ⟩ 
        ((Imp ●ₘ Prot) 〖 Exp 【 V 】 〗) ↓ ⊕ᵥ ~ M   ≈⟨ ≈ᵥ-refl ⟩
        (Γ₂,ᵥ ∘ Γ₂,ᵢ ∘ Γ₂,ₒ) V                         ∎
        where open EqReasoning 𝕍ₛ using (begin_; _∎; _≈⟨_⟩_)


-- Theorem 6
FixedPoint-Γ₀-Γ₂ : ∀ {X : RoutingMatrix} →
                   let V = ~ X
                       I = (Imp ●ₘ Prot) 〖 Exp 【 ~ X 】 〗
                       O = Exp 【 ~ X 】
                   in
                   X ≈ₘ (A 〔 X 〕 ⊕ₘ M) →
                   (V ≈ᵥ I ↓ ⊕ᵥ ~ M) ×
                   (I ≈ᵥ,₂ ((Imp ●ₘ Prot) 〖 O 〗) ×
                   (O ≈ᵥ,₂ (Exp 【 V 】)))
FixedPoint-Γ₀-Γ₂ {X} X=AX⊕M  = 
        (begin
            ~ X                 ≈⟨ ≈ₘ⇒≈ᵥ X=AX⊕M ⟩
            ~ (A 〔 X 〕 ⊕ₘ M)  ≈⟨ ≈ₘ⇒≈ᵥ ≈ₘ-refl ⟩
            ~ (Γ₀ X)            ≈⟨ ≈ᵥ-sym Γ₀=Γ₁ ⟩
            Γ₁ (~ X)            ≈⟨ Γ₁=Γ₂,ᵥ (~ X) ⟩
            Γ₂,ᵥ I              ≈⟨ ≈ᵥ-refl ⟩
            I ↓ ⊕ᵥ ~ M ∎) ,
        ≈ᵥ,₂-refl ,
        ≈ᵥ,₂-refl
        where
          open EqReasoning 𝕍ₛ
          I = (Imp ●ₘ Prot) 〖 Exp 【 ~ X 】 〗


postulate 
  lem1 : ∀ V I O → (Γ₂-Model ^ 3) (S₂ V I O)
                    ≈ₛ
                    S₂ ((Γ₂,ᵥ ∘ Γ₂,ᵢ ∘ Γ₂,ₒ) V) ((Γ₂,ᵢ ∘ Γ₂,ₒ ∘ Γ₂,ᵥ) I) ((Γ₂,ₒ ∘ Γ₂,ᵥ ∘ Γ₂,ᵢ) O)
  
  lem2 : ∀ V I O k → (Γ₂-Model ^ (3 * k)) (S₂ V I O)
                      ≈ₛ
                      S₂ (((Γ₂,ᵥ ∘ Γ₂,ᵢ ∘ Γ₂,ₒ) ^ k) V) (((Γ₂,ᵢ ∘ Γ₂,ₒ ∘ Γ₂,ᵥ) ^ k) I) (((Γ₂,ₒ ∘ Γ₂,ᵥ ∘ Γ₂,ᵢ) ^ k) O) -- induction using lem1 

  lem3 : ∀ k V  → ((Γ₂,ᵥ ∘ Γ₂,ᵢ ∘ Γ₂,ₒ) ^ k) V ≈ᵥ (Γ₁ ^ k)  V -- induction using Γ₁=Γ₂,ᵥ

  lem4 : ∀ k I  → ((Γ₂,ᵢ ∘ Γ₂,ₒ ∘ Γ₂,ᵥ) ^ (suc k)) I ≈ᵥ,₂ (Γ₂,ᵢ ∘ Γ₂,ₒ ∘ (Γ₁ ^ k) ∘ Γ₂,ᵥ) I  -- induction using lem3 

  lem5 : ∀ k O  → ((Γ₂,ₒ ∘ Γ₂,ᵥ ∘ Γ₂,ᵢ) ^ (suc k)) O ≈ᵥ,₂ (Γ₂,ₒ ∘ (Γ₁ ^ k) ∘ Γ₂,ᵥ ∘ Γ₂,ᵢ) O -- induction using lem3 

  lem6 : ∀ k V I O → (Γ₂-Model ^ (3 * (suc k))) (S₂ V I O)
                      ≈ₛ
                      S₂ ((Γ₁ ^ (suc k)) V) ((Γ₂,ᵢ ∘ Γ₂,ₒ ∘ (Γ₁ ^ k) ∘ Γ₂,ᵥ) I) ((Γ₂,ₒ ∘ (Γ₁ ^ k) ∘ Γ₂,ᵥ ∘ Γ₂,ᵢ) O)

  lem7 : ∀ k → (Γ₂,ᵢ ∘ Γ₂,ₒ ∘ (Γ₁ ^ k) ∘ Γ₂,ᵥ) Øᵥ,₂ ≈ᵥ,₂ (Γ₂,ᵢ ∘ Γ₂,ₒ ∘ (Γ₁ ^ k)) (~ M)   -- Γ₂,ᵥ Øᵥ,₂ ≈ᵥ,₂ ~ M

  lem8 : ∀ k →  (Γ₂,ₒ ∘ (Γ₁ ^ k) ∘ Γ₂,ᵥ ∘ Γ₂,ᵢ) Øᵥ,₂ ≈ᵥ,₂ (Γ₂,ₒ ∘ (Γ₁ ^ k)) (~ M)       -- (Γ₂,ᵥ ∘ Γ₂,ᵢ) Øᵥ,₂ ≈ᵥ,₂ ~ M 

  Γ₁=Γ₂ : ∀ k → (Γ₂-Model ^ (3 * (suc k))) (S₂ (~ M) Øᵥ,₂ Øᵥ,₂) ≈ₛ S₂ ((Γ₁ ^ (suc k)) (~ M)) ((Γ₂,ᵢ ∘ Γ₂,ₒ) ((Γ₁ ^ k) (~ M))) (Γ₂,ₒ ((Γ₁ ^ k) (~ M)))

  Γ₀=Γ₂ : ∀ k → (Γ₂-Model ^ (3 * (suc k))) (S₂ (~ M) Øᵥ,₂ Øᵥ,₂) ≈ₛ S₂ (~ ((Γ₀ ^ (suc k)) M)) ((Γ₂,ᵢ ∘ Γ₂,ₒ)  (~ ((Γ₀ ^ k) M))) (Γ₂,ₒ (~ ((Γ₀ ^ k) M)))
        

private
  Lemma1 : ∀ {A : RoutingMatrix} → Γ₂,ₒ (Øᵥ,₂ ↓ ⊕ᵥ ~ A) ≈ᵥ,₂ Γ₂,ₒ (~ A)
  Lemma1 {A} = Γ₂,ₒ-cong (≈ᵥ-trans (⊕ᵥ-cong Øᵥ,₂↓=Øᵥ (≈ₘ⇒≈ᵥ ≈ₘ-refl))
                                 (Øᵥ-identityₗ {~ A}))
  Lemma2 : ∀ {A} → (Γ₂,ᵢ ∘ Γ₂,ₒ) (Øᵥ,₂ ↓ ⊕ᵥ ~ A) ≈ᵥ,₂ (Γ₂,ᵢ ∘ Γ₂,ₒ) (~ A)
  Lemma2 = Γ₂,ᵢ-cong Lemma1

  Lemma3 : ∀ {a a'} → {s : Γ₂-State} → a ≡ a' → (Γ₂-Model ^ a) s ≈ₛ (Γ₂-Model ^ a') s
  Lemma3 {zero} {.zero} {s} refl = ≈ₛ-refl
  Lemma3 {suc a} {.(suc a)} {s} refl = Γ₂-cong (Lemma3 {a} {a} refl)

  Lemma4 : ∀ {k} → 3 * (suc (suc k)) ≡ 3 + (3 * suc k)
  Lemma4 {zero} = refl
  Lemma4 {suc k} =
    3 * (suc (suc (suc k))) ≡⟨ *-comm 3 (suc (suc (suc k))) ⟩
    (suc (suc (suc k))) * 3 ≡⟨ refl ⟩
    3 + (suc (suc k)) * 3   ≡⟨ cong (3 +_) (*-comm (suc (suc k)) 3) ⟩
    3 + (3 * suc (suc k)) ∎
    where open PropositionalEq.≡-Reasoning


-- -- Theorem 7
-- Γ₁=Γ₂ : ∀ {k} → let I' = (Γ₂,ᵢ ∘ Γ₂,ₒ) ((Γ₁ ^ k) (~ M))
--                     O' = Γ₂,ₒ ((Γ₁ ^ k) (~ M)) in
--         (Γ₂-Model ^ (3 * (suc k))) (S₂ (~ M) Øᵥ,₂ Øᵥ,₂) ≈ₛ
--         S₂ ((Γ₁ ^ (suc k)) (~ M)) I' O'
-- Γ₁=Γ₂ {zero} = begin
--         (Γ₂-Model ^ 3) (S₂ (~ M) Øᵥ,₂ Øᵥ,₂)
--           ≈⟨ ≈ₛ-refl ⟩
--         S₂ ((Γ₂,ᵥ ∘ Γ₂,ᵢ ∘ Γ₂,ₒ) (~ M))
--              ((Γ₂,ᵢ ∘ Γ₂,ₒ) (Øᵥ,₂ ↓ ⊕ᵥ ~ M))
--              (Γ₂,ₒ (Øᵥ,₂ ↓ ⊕ᵥ ~ M))
--           ≈⟨ ≈ᵥ-sym (Γ₁=Γ₂,ᵥ (~ M)) , Lemma2 , Lemma1  ⟩ 
--         S₂ (Γ₁ (~ M)) ((Γ₂,ᵢ ∘ Γ₂,ₒ) (~ M)) (Γ₂,ₒ (~ M)) ∎
--         where open EqReasoning 𝕊ₛ
-- Γ₁=Γ₂ {suc k} = begin
--         (Γ₂-Model ^ (3 * suc (suc k)))
--         (S₂ (~ M) Øᵥ,₂ Øᵥ,₂)
--           ≈⟨ Lemma3 (Lemma4 {k}) ⟩
--         (Γ₂-Model ^ 3) ((Γ₂-Model ^ (3 * (suc k)))
--         (S₂ (~ M) Øᵥ,₂ Øᵥ,₂))
--           ≈⟨ Γ₂-iter-cong {3} (Γ₁=Γ₂ {k}) ⟩
--         (Γ₂-Model ^ 3)
--         (S₂ ((Γ₁ ^ (suc k)) (~ M))
--               ((Γ₂,ᵢ ∘ Γ₂,ₒ) ((Γ₁ ^ k) (~ M)))
--               (Γ₂,ₒ ((Γ₁ ^ k) (~ M))))
--           ≈⟨ {!!}
--               -- Γ₂-iter-cong {2}
--               --    {Γ₂-Model (record {V = (Γ₁ ^ (suc k)) (~ M);
--               --                       I = (Γ₂,ᵢ ∘ Γ₂,ₒ) ((Γ₁ ^ k) (~ M));
--               --                       O = Γ₂,ₒ ((Γ₁ ^ k) (~ M))})}
--               --    {(record {         V = (Γ₁ ^ (suc k)) (~ M);
--               --                       I = (Γ₂,ᵢ ∘ Γ₂,ₒ) ((Γ₁ ^ k) (~ M));
--               --                       O = Γ₂,ₒ ((Γ₁ ^ (suc k)) (~ M))})}
--               --    (≈ᵥ-sym (Γ₁=Γ₂,ᵥ {k} {M}) , ≈ᵥ,₂-refl {n} {n} , ≈ᵥ,₂-refl {n} {n})
--           ⟩
--         (Γ₂-Model ^ 2)
--         (S₂ ((Γ₁ ^ (suc k)) (~ M))
--             ((Γ₂,ᵢ ∘ Γ₂,ₒ) ((Γ₁ ^ k) (~ M)))
--             O')
--           ≈⟨ {!!} 

--               -- Γ₂-iter-cong {1}
--               --    {Γ₂-Model (record {V = (Γ₁ ^ (suc k)) (~ M);
--               --                       I = (Γ₂,ᵢ ∘ Γ₂,ₒ) ((Γ₁ ^ k) (~ M));
--               --                       O = Γ₂,ₒ ((Γ₁ ^ (suc k)) (~ M))})}
--               --    {(record {         V = (Γ₁ ^ (suc k)) (~ M);
--               --                       I = (Γ₂,ᵢ ∘ Γ₂,ₒ) ((Γ₁ ^ (suc k)) (~ M));
--               --                       O = Γ₂,ₒ ((Γ₁ ^ (suc k)) (~ M))})}
--               --    (≈ᵥ-sym (Γ₁=Γ₂,ᵥ {k} {M}) , ≈ᵥ,₂-refl , ≈ᵥ,₂-refl)
--            ⟩
--         Γ₂-Model
--         (S₂ ((Γ₁ ^ (suc k)) (~ M)) I' O')
--           ≈⟨ {!!} ⟩ -- ≈⟨ ≈ᵥ-sym (Γ₁=Γ₂,ᵥ {suc k} {M}) , ≈ᵥ,₂-refl , ≈ᵥ,₂-refl ⟩
--         S₂ ((Γ₁ ^ suc (suc k)) (~ M)) I' O' ∎
--         where open EqReasoning 𝕊ₛ
--               I' = (Γ₂,ᵢ ∘ Γ₂,ₒ) ((Γ₁ ^ suc k) (~ M))
--               O' = Γ₂,ₒ ((Γ₁ ^ suc k) (~ M))
