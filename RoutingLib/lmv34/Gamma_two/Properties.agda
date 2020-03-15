open import Algebra.Core using (Op₂)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_,_; _×_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Function using (_∘_)
open import Level using (_⊔_)
open import Data.List using (List; filter; tabulate; []; _∷_; map)
open import Data.Nat using (zero; suc; ℕ; _*_; _+_)
open import Data.Nat.Properties using (*-comm; *-distribˡ-+)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary.Negation using (¬?; contradiction)
open import Relation.Binary using (Setoid; DecSetoid; Rel; Reflexive; Symmetric; Transitive; _⇒_)
open import Relation.Binary.PropositionalEquality as PropositionalEq using (_≡_; refl; cong)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import RoutingLib.Iteration.Synchronous using (_^_)
open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
open import RoutingLib.Routing as Routing using () renaming (AdjacencyMatrix to AdjacencyMatrix')
import RoutingLib.lmv34.Gamma_zero as Gamma_zero
import RoutingLib.lmv34.Gamma_zero.Algebra as Gamma_zero_Algebra
import RoutingLib.lmv34.Gamma_one as Gamma_one
import RoutingLib.lmv34.Gamma_one.Algebra as Gamma_one_Algebra
import RoutingLib.lmv34.Gamma_one.Properties as Gamma_one_Properties
import RoutingLib.lmv34.Gamma_two as Gamma_two 
import RoutingLib.lmv34.Gamma_two.Algebra as Gamma_two_Algebra

module RoutingLib.lmv34.Gamma_two.Properties
  {a b ℓ} {alg : RawRoutingAlgebra a b ℓ}
  (isRAlg : IsRoutingAlgebra alg) {n}
  (A    : AdjacencyMatrix' alg n)
  (Imp Prot Exp : Gamma_two_Algebra.RouteMapMatrix isRAlg n )
  (A=Imp∘Prot∘Exp : Gamma_two_Algebra.IsComposition isRAlg n A Imp Prot Exp)
  where

open RawRoutingAlgebra alg
open Routing alg n renaming (I to M) using (RoutingMatrix; _≈ₘ_; ≈ₘ-refl)

open Gamma_zero alg A
open Gamma_zero_Algebra alg n

open Gamma_one isRAlg A
open Gamma_one_Algebra isRAlg n
open Gamma_one_Properties isRAlg A

open Gamma_two_Algebra isRAlg n
open Gamma_two isRAlg Imp Prot Exp

open DecSetoid FinRoute-decSetoid using () renaming (_≈_ to _≈ᵣ_)

import RoutingLib.Data.Matrix.Relation.Binary.Equality as MatrixEquality

------------------------------------
------------------------------------
-- Operation properties

-- RoutingVector₂ setoid
open MatrixEquality ↭-setoid public using (𝕄ₛ) renaming
       ( _≈ₘ_             to _≈ᵥ,₂_
       ; ≈ₘ-reflexive     to ≈ᵥ,₂-reflexive
       ; ≈ₘ-refl          to ≈ᵥ,₂-refl
       ; ≈ₘ-sym           to ≈ᵥ,₂-sym
       ; ≈ₘ-trans         to ≈ᵥ,₂-trans
       ; ≈ₘ-isEquivalence to ≈ᵥ,₂-isEquivalence
       )
𝕍₂ₛ = 𝕄ₛ n n

【】-cong : ∀ {F V V'} → V ≈ᵥ V' → (F 【 V 】) ≈ᵥ,₂ (F 【 V' 】)
【】-cong V=V' i j = []-cong (V=V' i)

〖〗-cong : ∀ {F O O'} → O ≈ᵥ,₂ O' → (F 〖 O 〗) ≈ᵥ,₂ (F 〖 O' 〗)
〖〗-cong O=O' i j = []-cong (O=O' j i)

f[]-cong : ∀ {f f' : Route → Route} → {X : RoutingSet} →
           f ≈ₐ f' → f [ X ] ↭ f' [ X ]
f[]-cong {f} {f'} {X} f=f' = †-cong (lemma {xs = X} f=f')
   where lemma : {f g : Route → Route} → {xs : RoutingSet} →
                 (∀ r → f r ≈ g r) → map₂ f xs ↭ map₂ g xs
         lemma {f} {g} {[]} f=g = ↭-refl
         lemma {f} {g} {(d , v) ∷ xs} f=g = prep (refl , f=g v) (lemma {xs = xs} f=g)

A〚〛-cong : ∀ {F F' V} → (toRouteMapMatrix F) ≈ₐ,₂ (toRouteMapMatrix F') → F 〚 V 〛 ≈ᵥ  F' 〚 V 〛
A〚〛-cong {F} {F'} {V} F=F' i = ⨁ₛ-cong (λ {q} → f[]-cong {X = V q} (F=F' i q))

↓-cong : ∀ {I I'} → I ≈ᵥ,₂ I' → I ↓ ≈ᵥ I' ↓
↓-cong I=I' i = ⨁ₛ-cong (λ {q} → I=I' i q)

Øᵥ,₂↓=Øᵥ : Øᵥ,₂ ↓ ≈ᵥ Øᵥ
Øᵥ,₂↓=Øᵥ i = lemma n
  where lemma : ∀ k → ⨁ₛ (λ (q : Fin k) → []) ↭ []
        lemma zero = ↭-refl
        lemma (suc k) = ↭-trans (⊕ₛ-identityₗ (⨁ₛ (λ (q : Fin k) → []))) (lemma k)

Γ₂,ᵥØ=~M : Γ₂,ᵥ Øᵥ,₂ ≈ᵥ ~ M
Γ₂,ᵥØ=~M = begin
         Γ₂,ᵥ Øᵥ,₂ ≈⟨ ≈ᵥ-refl ⟩
         Øᵥ,₂ ↓ ⊕ᵥ ~ M ≈⟨ ⊕ᵥ-cong {Øᵥ,₂ ↓} {Øᵥ} {~ M} {~ M} Øᵥ,₂↓=Øᵥ ≈ᵥ-refl ⟩
         Øᵥ ⊕ᵥ ~ M ≈⟨ ⊕ᵥ-identityₗ (~ M) ⟩
         ~ M ∎
         where open EqReasoning 𝕍ₛ

Γ₂,ᵥ-cong : ∀ {I I'} → I ≈ᵥ,₂ I' → Γ₂,ᵥ I ≈ᵥ Γ₂,ᵥ I'
Γ₂,ᵥ-cong {I} {I'} I=I' = ⊕ᵥ-cong (↓-cong I=I') (≈ₘ⇒≈ᵥ ≈ₘ-refl)

Γ₂,ᵢ-cong : ∀ {O O'} → O ≈ᵥ,₂ O' → Γ₂,ᵢ O ≈ᵥ,₂ Γ₂,ᵢ O'
Γ₂,ᵢ-cong = 〖〗-cong

Γ₂,ₒ-cong : ∀ {V V'} → V ≈ᵥ V' → Γ₂,ₒ V ≈ᵥ,₂ Γ₂,ₒ V'
Γ₂,ₒ-cong = 【】-cong

Γ₂-comp-cong : ∀ {V V'} → V ≈ᵥ V' → (Γ₂,ᵥ ∘ Γ₂,ᵢ ∘ Γ₂,ₒ) V ≈ᵥ (Γ₂,ᵥ ∘ Γ₂,ᵢ ∘ Γ₂,ₒ) V'
Γ₂-comp-cong V=V' = (Γ₂,ᵥ-cong ∘ Γ₂,ᵢ-cong ∘ Γ₂,ₒ-cong) V=V'


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


Γ₂-cong : ∀ {S S'} → S ≈ₛ S' → Γ₂ S ≈ₛ Γ₂ S'
Γ₂-cong (V=V' , I=I' , O=O') = Γ₂,ᵥ-cong I=I' , Γ₂,ᵢ-cong O=O' , Γ₂,ₒ-cong V=V'

Γ₂-iter-cong : ∀ {S S'} k → S ≈ₛ S' → (Γ₂ ^ k) S ≈ₛ (Γ₂ ^ k) S'
Γ₂-iter-cong zero S=S' = S=S'
Γ₂-iter-cong (suc k) S=S' = Γ₂-cong (Γ₂-iter-cong k S=S')

Γ₂-iter-equiv : ∀ {a a' s} → a ≡ a' → (Γ₂ ^ a) s ≈ₛ (Γ₂ ^ a') s
Γ₂-iter-equiv {a} {.a} {s} refl = Γ₂-iter-cong a ≈ₛ-refl

------------------------------------
-- Theorems

-- Theorem 5
FixedPoint-Γ₂ : ∀ {V I O} →
                Γ₂ (S₂ V I O) ≈ₛ S₂ V I O →
                (V ≈ᵥ I ↓ ⊕ᵥ ~ M) ×
                (I ≈ᵥ,₂ ((Imp ●ₘ Prot) 〖 O 〗)) ×
                (O ≈ᵥ,₂ (Exp 【 V 】))
FixedPoint-Γ₂ (V=V , I=I , O=O) = ≈ᵥ-sym V=V , ≈ᵥ,₂-sym I=I , ≈ᵥ,₂-sym O=O

private
  postulate
    ▷-fixedPoint : ∀ (f : Route → Route) s → s ≈ ∞# → f s ≈ ∞# -- need this to prove LemmaA₃

LemmaA₃ : ∀ (f g : (Route → Route)) → (X : RoutingSet) →
            f [ g [ X ] ] ↭ (f ● g) [ X ]
LemmaA₃ f g [] = ↭-refl
LemmaA₃ f g ((d , v) ∷ X) with
      g v ≟ ∞#
... | yes gv=∞ = prf
    where
      prf : f [ g [ X ] ] ↭ (f ● g) [ (d , v) ∷ X ]
      prf with
            f (g v) ≟ ∞#
      ... | no fg≠∞  = contradiction (▷-fixedPoint f (g v) gv=∞) fg≠∞
      ... | yes _    = LemmaA₃ f g X
... | no _  = prf
    where
      prf : f [(d , g v) ∷ (g [ X ])] ↭ (f ● g) [ (d , v) ∷ X ]
      prf with
            f (g v) ≟ ∞#
      ... | yes _ = LemmaA₃ f g X
      ... | no _  = prep (refl , ≈-refl) (LemmaA₃ f g X)

-- tgg : temporary hack??? 
infix 10 _||_||
_||_|| : RouteMapMatrix → RoutingVector → RoutingVector
(A || V || ) i = ⨁ₛ (λ q → (A i q) [ V q ])

A||V||-cong : ∀ {F F' V} → F ≈ₐ,₂ F' → F || V || ≈ᵥ  F' || V ||
A||V||-cong {F} {F'} {V} F=F' i = ⨁ₛ-cong (λ {q} → f[]-cong {X = V q} (F=F' i q))

〚〛=|| : ∀ {A V} → A 〚 V 〛 ≈ᵥ (toRouteMapMatrix A) || V ||
〚〛=|| {A} {V} = ≈ᵥ-refl

LemmaA₄ : ∀ F G V → (F 〖 G 【 V 】 〗) ↓ ≈ᵥ (F ●ₘ (G ᵀ)) || V ||
LemmaA₄ F G V i = begin
   ((F 〖 G 【 V 】 〗) ↓) i ↭⟨ ↭-refl ⟩
   ⨁ₛ (λ q → (F i q) [ (G q i) [ V q ] ]) ↭⟨ ⨁ₛ-cong (λ {q} → (LemmaA₃ (F i q) (G q i) (V q))) ⟩
   ⨁ₛ (λ q → ((F i q) ● (G q i)) [ V q ]) ↭⟨ ↭-refl ⟩
   ((F ●ₘ (G ᵀ)) || V ||) i ∎
   where open PermutationReasoning

Γ₁=Γ₂-comp : ∀ (V : RoutingVector) → Γ₁ V ≈ᵥ (Γ₂,ᵥ ∘ Γ₂,ᵢ ∘ Γ₂,ₒ) V 
Γ₁=Γ₂-comp V = begin 
        Γ₁ V                                          ≈⟨ ≈ᵥ-refl ⟩
        A 〚 V 〛 ⊕ᵥ ~ M                              ≈⟨ ⊕ᵥ-cong (〚〛=|| {A} {V}) (≈ₘ⇒≈ᵥ ≈ₘ-refl) ⟩ 
        ((toRouteMapMatrix A) || V || ) ⊕ᵥ ~ M        ≈⟨ ⊕ᵥ-cong (A||V||-cong {V = V} A=Imp∘Prot∘Exp) (≈ₘ⇒≈ᵥ ≈ₘ-refl) ⟩
        ((Imp ●ₘ Prot) ●ₘ (Exp ᵀ)) || V || ⊕ᵥ ~ M     ≈⟨ ⊕ᵥ-cong (≈ᵥ-sym (LemmaA₄ (Imp ●ₘ Prot) Exp V)) (≈ₘ⇒≈ᵥ ≈ₘ-refl)   ⟩ 
        ((Imp ●ₘ Prot) 〖 Exp 【 V 】 〗) ↓ ⊕ᵥ ~ M    ≈⟨ ≈ᵥ-refl ⟩
        (Γ₂,ᵥ ∘ Γ₂,ᵢ ∘ Γ₂,ₒ) V                        ∎
        where open EqReasoning 𝕍ₛ using (begin_; _∎; step-≈)

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
            Γ₁ (~ X)            ≈⟨ Γ₁=Γ₂-comp (~ X) ⟩
            Γ₂,ᵥ I              ≈⟨ ≈ᵥ-refl ⟩
            I ↓ ⊕ᵥ ~ M ∎) ,
        ≈ᵥ,₂-refl ,
        ≈ᵥ,₂-refl
        where
          open EqReasoning 𝕍ₛ
          I = (Imp ●ₘ Prot) 〖 Exp 【 ~ X 】 〗

private
    lem1 : ∀ V I O → (Γ₂ ^ 3) (S₂ V I O)
                      ≈ₛ
                      S₂ ((Γ₂,ᵥ ∘ Γ₂,ᵢ ∘ Γ₂,ₒ) V) ((Γ₂,ᵢ ∘ Γ₂,ₒ ∘ Γ₂,ᵥ) I) ((Γ₂,ₒ ∘ Γ₂,ᵥ ∘ Γ₂,ᵢ) O)
    lem1 V I O = ≈ₛ-refl

    lem2 : ∀ V I O k → (Γ₂ ^ (3 * k)) (S₂ V I O)
                        ≈ₛ
                        S₂ (((Γ₂,ᵥ ∘ Γ₂,ᵢ ∘ Γ₂,ₒ) ^ k) V) (((Γ₂,ᵢ ∘ Γ₂,ₒ ∘ Γ₂,ᵥ) ^ k) I) (((Γ₂,ₒ ∘ Γ₂,ᵥ ∘ Γ₂,ᵢ) ^ k) O)
    lem2 V I O zero    = ≈ₛ-refl
    lem2 V I O (suc k) = begin
            (Γ₂ ^ (3 * suc k)) (S₂ V I O)                ≈⟨ Γ₂-iter-equiv (lem k) ⟩
            ((Γ₂ ^ 3) ∘ (Γ₂ ^ (3 * k))) (S₂ V I O) ≈⟨ Γ₂-iter-cong 3 (lem2 V I O k) ⟩
            S₂ (((Γ₂,ᵥ ∘ Γ₂,ᵢ ∘ Γ₂,ₒ) ^ suc k) V) (((Γ₂,ᵢ ∘ Γ₂,ₒ ∘ Γ₂,ᵥ) ^ suc k) I) (((Γ₂,ₒ ∘ Γ₂,ᵥ ∘ Γ₂,ᵢ) ^ suc k) O) ∎
            where open EqReasoning 𝕊ₛ
                  lem : ∀ k → 3 * suc k ≡ 3 + (3 * k)
                  lem k = *-distribˡ-+ 3 1 k

    lem3 : ∀ k V  → ((Γ₂,ᵥ ∘ Γ₂,ᵢ ∘ Γ₂,ₒ) ^ k) V ≈ᵥ (Γ₁ ^ k) V
    lem3 zero V    = ≈ᵥ-refl
    lem3 (suc k) V = begin
            ((Γ₂,ᵥ ∘ Γ₂,ᵢ ∘ Γ₂,ₒ) ^ suc k) V  ≈⟨ Γ₂-comp-cong (lem3 k V) ⟩
            (Γ₂,ᵥ ∘ Γ₂,ᵢ ∘ Γ₂,ₒ) ((Γ₁ ^ k) V) ≈⟨ ≈ᵥ-sym (Γ₁=Γ₂-comp ((Γ₁ ^ k) V)) ⟩
            (Γ₁ ^ suc k) V ∎
            where open EqReasoning 𝕍ₛ

    lem4 : ∀ k I  → ((Γ₂,ᵢ ∘ Γ₂,ₒ ∘ Γ₂,ᵥ) ^ (suc k)) I ≈ᵥ,₂ (Γ₂,ᵢ ∘ Γ₂,ₒ ∘ (Γ₁ ^ k) ∘ Γ₂,ᵥ) I
    lem4 zero I    = ≈ᵥ,₂-refl
    lem4 (suc k) I = begin
            ((Γ₂,ᵢ ∘ Γ₂,ₒ ∘ Γ₂,ᵥ) ^ (suc (suc k))) I ≈⟨ ≈ᵥ,₂-refl ⟩
            (Γ₂,ᵢ ∘ Γ₂,ₒ ∘ Γ₂,ᵥ ∘ ((Γ₂,ᵢ ∘ Γ₂,ₒ ∘ Γ₂,ᵥ) ^ (suc k))) I ≈⟨ (Γ₂,ᵢ-cong ∘ Γ₂,ₒ-cong ∘ Γ₂,ᵥ-cong) (lem4 k I) ⟩
            (Γ₂,ᵢ ∘ Γ₂,ₒ ∘ Γ₂,ᵥ ∘ ((Γ₂,ᵢ ∘ Γ₂,ₒ ∘ (Γ₁ ^ k) ∘ Γ₂,ᵥ))) I ≈⟨ ≈ᵥ,₂-refl ⟩
            (Γ₂,ᵢ ∘ Γ₂,ₒ ∘ Γ₂,ᵥ ∘ Γ₂,ᵢ ∘ Γ₂,ₒ ∘ (Γ₁ ^ k) ∘ Γ₂,ᵥ) I ≈⟨ (Γ₂,ᵢ-cong ∘ Γ₂,ₒ-cong) (lem3 1 (((Γ₁ ^ k) ∘ Γ₂,ᵥ) I)) ⟩
            (Γ₂,ᵢ ∘ Γ₂,ₒ ∘ Γ₁ ∘ (Γ₁ ^ k) ∘ Γ₂,ᵥ) I ≈⟨ ≈ᵥ,₂-refl ⟩
            (Γ₂,ᵢ ∘ Γ₂,ₒ ∘ (Γ₁ ^ suc k) ∘ Γ₂,ᵥ) I  ∎
            where open EqReasoning 𝕍₂ₛ

    lem5 : ∀ k O  → ((Γ₂,ₒ ∘ Γ₂,ᵥ ∘ Γ₂,ᵢ) ^ (suc k)) O ≈ᵥ,₂ (Γ₂,ₒ ∘ (Γ₁ ^ k) ∘ Γ₂,ᵥ ∘ Γ₂,ᵢ) O
    lem5 zero O    = ≈ᵥ,₂-refl
    lem5 (suc k) O = begin
            ((Γ₂,ₒ ∘ Γ₂,ᵥ ∘ Γ₂,ᵢ) ^ (suc (suc k))) O ≈⟨ ≈ᵥ,₂-refl ⟩
            (Γ₂,ₒ ∘ Γ₂,ᵥ ∘ Γ₂,ᵢ ∘ ((Γ₂,ₒ ∘ Γ₂,ᵥ ∘ Γ₂,ᵢ) ^ (suc k))) O ≈⟨ (Γ₂,ₒ-cong ∘ Γ₂,ᵥ-cong ∘ Γ₂,ᵢ-cong) (lem5 k O) ⟩
            (Γ₂,ₒ ∘ Γ₂,ᵥ ∘ Γ₂,ᵢ ∘ ((Γ₂,ₒ ∘ (Γ₁ ^ k) ∘ Γ₂,ᵥ ∘ Γ₂,ᵢ))) O ≈⟨ ≈ᵥ,₂-refl ⟩
            (Γ₂,ₒ ∘ Γ₂,ᵥ ∘ Γ₂,ᵢ ∘ Γ₂,ₒ ∘ (Γ₁ ^ k) ∘ Γ₂,ᵥ ∘ Γ₂,ᵢ) O ≈⟨ (Γ₂,ₒ-cong) (lem3 1 (((Γ₁ ^ k) ∘ Γ₂,ᵥ ∘ Γ₂,ᵢ) O)) ⟩
            (Γ₂,ₒ ∘ Γ₁ ∘ (Γ₁ ^ k) ∘ Γ₂,ᵥ ∘ Γ₂,ᵢ) O ≈⟨ ≈ᵥ,₂-refl ⟩
            (Γ₂,ₒ ∘ (Γ₁ ^ suc k) ∘ Γ₂,ᵥ ∘ Γ₂,ᵢ) O  ∎
            where open EqReasoning 𝕍₂ₛ

    lem6 : ∀ k V I O → (Γ₂ ^ (3 * (suc k))) (S₂ V I O)
                        ≈ₛ
                        S₂ ((Γ₁ ^ (suc k)) V) ((Γ₂,ᵢ ∘ Γ₂,ₒ ∘ (Γ₁ ^ k) ∘ Γ₂,ᵥ) I) ((Γ₂,ₒ ∘ (Γ₁ ^ k) ∘ Γ₂,ᵥ ∘ Γ₂,ᵢ) O)
    lem6 k V I O = begin
            (Γ₂ ^ (3 * (suc k))) (S₂ V I O) ≈⟨ lem2 V I O (suc k) ⟩
            S₂ (((Γ₂,ᵥ ∘ Γ₂,ᵢ ∘ Γ₂,ₒ) ^ suc k) V) (((Γ₂,ᵢ ∘ Γ₂,ₒ ∘ Γ₂,ᵥ) ^ suc k) I) (((Γ₂,ₒ ∘ Γ₂,ᵥ ∘ Γ₂,ᵢ) ^ suc k) O)
              ≈⟨ lem3 (suc k) V , lem4 k I , lem5 k O ⟩
            S₂ ((Γ₁ ^ (suc k)) V) ((Γ₂,ᵢ ∘ Γ₂,ₒ ∘ (Γ₁ ^ k) ∘ Γ₂,ᵥ) I) ((Γ₂,ₒ ∘ (Γ₁ ^ k) ∘ Γ₂,ᵥ ∘ Γ₂,ᵢ) O) ∎
            where open EqReasoning 𝕊ₛ

    lem7 : ∀ k → (Γ₂,ᵢ ∘ Γ₂,ₒ ∘ (Γ₁ ^ k) ∘ Γ₂,ᵥ) Øᵥ,₂ ≈ᵥ,₂ (Γ₂,ᵢ ∘ Γ₂,ₒ ∘ (Γ₁ ^ k)) (~ M)
    lem7 k = (Γ₂,ᵢ-cong ∘ Γ₂,ₒ-cong ∘ (Γ₁-iter-cong k)) Γ₂,ᵥØ=~M

    lem8 : ∀ k →  (Γ₂,ₒ ∘ (Γ₁ ^ k) ∘ Γ₂,ᵥ ∘ Γ₂,ᵢ) Øᵥ,₂ ≈ᵥ,₂ (Γ₂,ₒ ∘ (Γ₁ ^ k)) (~ M) 
    lem8 k = (Γ₂,ₒ-cong ∘ (Γ₁-iter-cong k)) Γ₂,ᵥØ=~M

Γ₁=Γ₂ : ∀ k → (Γ₂ ^ (3 * (suc k))) (S₂ (~ M) Øᵥ,₂ Øᵥ,₂) ≈ₛ
              S₂ ((Γ₁ ^ (suc k)) (~ M)) ((Γ₂,ᵢ ∘ Γ₂,ₒ) ((Γ₁ ^ k) (~ M))) (Γ₂,ₒ ((Γ₁ ^ k) (~ M)))
Γ₁=Γ₂ k = begin
  (Γ₂ ^ (3 * (suc k))) (S₂ (~ M) Øᵥ,₂ Øᵥ,₂)
            ≈⟨ lem6 k (~ M) Øᵥ,₂ Øᵥ,₂ ⟩
  S₂ ((Γ₁ ^ (suc k)) (~ M)) ((Γ₂,ᵢ ∘ Γ₂,ₒ ∘ (Γ₁ ^ k) ∘ Γ₂,ᵥ) Øᵥ,₂) ((Γ₂,ₒ ∘ (Γ₁ ^ k) ∘ Γ₂,ᵥ ∘ Γ₂,ᵢ) Øᵥ,₂)
            ≈⟨ ≈ᵥ-refl , lem7 k , lem8 k ⟩
  S₂ ((Γ₁ ^ (suc k)) (~ M)) ((Γ₂,ᵢ ∘ Γ₂,ₒ) ((Γ₁ ^ k) (~ M))) (Γ₂,ₒ ((Γ₁ ^ k) (~ M))) ∎
  where open EqReasoning 𝕊ₛ

Γ₀=Γ₂ : ∀ k → (Γ₂ ^ (3 * (suc k))) (S₂ (~ M) Øᵥ,₂ Øᵥ,₂) ≈ₛ
              S₂ (~ ((Γ₀ ^ (suc k)) M)) ((Γ₂,ᵢ ∘ Γ₂,ₒ) (~ ((Γ₀ ^ k) M))) (Γ₂,ₒ (~ ((Γ₀ ^ k) M)))
Γ₀=Γ₂ k = begin
  (Γ₂ ^ (3 * (suc k))) (S₂ (~ M) Øᵥ,₂ Øᵥ,₂) ≈⟨ Γ₁=Γ₂ k ⟩
  S₂ ((Γ₁ ^ (suc k)) (~ M)) ((Γ₂,ᵢ ∘ Γ₂,ₒ) ((Γ₁ ^ k) (~ M))) (Γ₂,ₒ ((Γ₁ ^ k) (~ M)))
            ≈⟨ Γ₀=Γ₁-iter {suc k} {M} , (Γ₂,ᵢ-cong ∘ Γ₂,ₒ-cong) (Γ₀=Γ₁-iter {k} {M}) , Γ₂,ₒ-cong (Γ₀=Γ₁-iter {k} {M}) ⟩
  S₂ (~ ((Γ₀ ^ (suc k)) M)) ((Γ₂,ᵢ ∘ Γ₂,ₒ) (~ ((Γ₀ ^ k) M))) (Γ₂,ₒ (~ ((Γ₀ ^ k) M))) ∎
  where open EqReasoning 𝕊ₛ
