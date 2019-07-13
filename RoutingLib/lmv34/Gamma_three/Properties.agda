open import Algebra.FunctionProperties.Core using (Op₂)
open import Data.Fin using (Fin)
open import Data.Product using (_,_; _×_) renaming (proj₁ to π₁; proj₂ to π₂)
open import Data.List using (List; filter; tabulate; []; _∷_; _++_; map)
import Data.List.Membership.DecSetoid as Membership
open import Data.Nat using (zero; suc; ℕ; _*_; _+_)
open import Function using (_∘_)
open import Level using (_⊔_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction; ¬?)
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
import RoutingLib.lmv34.Gamma_two.Properties as Gamma_two_Properties
import RoutingLib.lmv34.Gamma_three as Gamma_three
import RoutingLib.lmv34.Gamma_three.Algebra as Gamma_three_Algebra

module RoutingLib.lmv34.Gamma_three.Properties
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
open Gamma_two_Properties isRAlg _●_ A Imp Prot Exp A=Imp∘Prot∘Exp
  hiding (_≈ₛ_; ≈ₛ-refl; ≈ₛ-sym; ≈ₛ-trans; 𝕊ₛ)
open Gamma_three isRAlg _●_ Imp Prot Exp
open Gamma_three_Algebra isRAlg n _●_

open DecSetoid FinRoute-decSetoid using () renaming (refl to ≈ᵣ-refl; _≟_ to _≟ᵣ_)
open Membership FinRoute-decSetoid using (_∈?_)

------------------------------------
-- Γ₃-State
infix 2 _≈ₛ_

_≈ₛ_ : Rel Γ₃-State (a ⊔ ℓ)
(S₃ V O I ∇,Δ) ≈ₛ (S₃ V' O' I' ∇,Δ') =
  V ≈ᵥ V'   ×
  O ≈ᵥ,₂ O' ×
  I ≈ᵥ,₂ I' ×
  π₁ ∇,Δ ≈ᵥ,₂ π₁ ∇,Δ' ×
  π₂ ∇,Δ ≈ᵥ,₂ π₂ ∇,Δ'

≈ₛ-refl : Reflexive _≈ₛ_
≈ₛ-refl = (≈ᵥ-refl , ≈ᵥ,₂-refl , ≈ᵥ,₂-refl , ≈ᵥ,₂-refl , ≈ᵥ,₂-refl)
≈ₛ-sym : Symmetric _≈ₛ_
≈ₛ-sym (V=V' , I=I' , O=O' , ∇=∇' , Δ=Δ') =
  (≈ᵥ-sym V=V' , ≈ᵥ,₂-sym I=I' , ≈ᵥ,₂-sym O=O' , ≈ᵥ,₂-sym ∇=∇' , ≈ᵥ,₂-sym Δ=Δ')
≈ₛ-trans : Transitive _≈ₛ_
≈ₛ-trans (V=V' , I=I' , O=O' , ∇=∇' , Δ=Δ') (V'=V'' , I'=I'' , O'=O'' , ∇'=∇'' , Δ'=Δ'') =
  (≈ᵥ-trans V=V' V'=V'' , ≈ᵥ,₂-trans I=I' I'=I'' , ≈ᵥ,₂-trans O=O' O'=O'' , ≈ᵥ,₂-trans ∇=∇' ∇'=∇'' , ≈ᵥ,₂-trans Δ=Δ' Δ'=Δ'')
  
𝕊ₛ : Setoid a (a ⊔ ℓ)
𝕊ₛ = record {Carrier = Γ₃-State;
             _≈_ = _≈ₛ_;
             isEquivalence =
               record {refl = ≈ₛ-refl; sym = ≈ₛ-sym; trans = ≈ₛ-trans}}


------------------------------------
-- Operation properties
++-cong : ∀ {A A' B B'} → A ↭ A' → B ↭ B' →
          A ++ B ↭ A' ++ B'
++-cong {[]} {[]} A=A' B=B'         = B=B'
++-cong {x ∷ A} {.x ∷ .A} refl B=B' = prep ≈ᵣ-refl (++-cong refl B=B') 
++-cong (trans A=A' A'=A'') B=B'    = trans (++-cong A=A' refl) (++-cong A'=A'' B=B')
++-cong (prep eq A=A') B=B'         = prep eq (++-cong A=A' B=B')
++-cong (swap eq₁ eq₂ A=A') B=B'    = swap eq₁ eq₂ (++-cong A=A' B=B')

postulate
  minus-cong : ∀ {A A' B B'} → A ↭ A' → B ↭ B' → A - B ↭ A' - B'

minusᵥ-cong : ∀ {U U' V V'} → U ≈ᵥ,₂ U' → V ≈ᵥ,₂ V' →
          (U -ᵥ V) ≈ᵥ,₂ (U' -ᵥ V')
minusᵥ-cong U=U' V=V' i j = minus-cong (U=U' i j) (V=V' i j)

∪-cong : ∀ {A A' B B'} → A ↭ A' → B ↭ B' →
         A ∪ B ↭ A' ∪ B'
∪-cong {A} {A'} {B} {B'} A=A' B=B' = ++-cong A=A' (minus-cong B=B' A=A')

∪ᵥ-cong : ∀ {U U' V V'} → U ≈ᵥ,₂ U' → V ≈ᵥ,₂ V' →
          (U ∪ᵥ V) ≈ᵥ,₂ (U' ∪ᵥ V')
∪ᵥ-cong U=U' V=V' i j = ∪-cong (U=U' i j) (V=V' i j)

diff-cong : ∀ {A A' B B'} → A ↭ A' → B ↭ B' →
            π₁ (diff A B) ↭ π₁ (diff A' B') ×
            π₂ (diff A B) ↭ π₂ (diff A' B')
diff-cong A=A' B=B' = minus-cong A=A' B=B' , minus-cong B=B' A=A'

diffᵥ-cong : ∀ {U U' V V'} → U ≈ᵥ,₂ U' → V ≈ᵥ,₂ V' →
            π₁ (diffᵥ U V) ≈ᵥ,₂ π₁ (diffᵥ U' V') ×
            π₂ (diffᵥ U V) ≈ᵥ,₂ π₂ (diffᵥ U' V')
diffᵥ-cong A=A' B=B' =
  (λ i j → minus-cong (A=A' i j) (B=B' i j)) ,
  (λ i j → minus-cong (B=B' i j) (A=A' i j))

[]-xs : ∀ xs → [] - xs ↭ []
[]-xs xs = ↭-refl

xs-[] : ∀ xs → xs - [] ↭ xs
xs-[] [] = ↭-refl
xs-[] (x ∷ xs) = prep ≈ᵣ-refl (xs-[] xs)

++-identityₗ : ∀ xs → [] ++ xs ↭ xs
++-identityₗ xs = ↭-refl

++-identityᵣ : ∀ xs → xs ++ [] ↭ xs
++-identityᵣ [] = ↭-refl
++-identityᵣ (x ∷ xs) = prep ≈ᵣ-refl (++-identityᵣ xs)

∪-identityₗ : ∀ xs → [] ∪ xs ↭ xs
∪-identityₗ xs = xs-[] xs

∪-identityᵣ : ∀ xs → xs ∪ [] ↭ xs
∪-identityᵣ xs = ++-identityᵣ xs

Γ₃,ᵥ-cong : ∀ {I I'} → I ≈ᵥ,₂ I' → Γ₃,ᵥ I ≈ᵥ Γ₃,ᵥ I'
Γ₃,ᵥ-cong = Γ₂,ᵥ-cong

Γ₃,ᵢ-cong : ∀ {I I' ∇ ∇' Δ Δ'} → I ≈ᵥ,₂ I' → ∇ ≈ᵥ,₂ ∇' → Δ ≈ᵥ,₂ Δ' →
            Γ₃,ᵢ I (∇ , Δ) ≈ᵥ,₂ Γ₃,ᵢ I' (∇' , Δ')
Γ₃,ᵢ-cong I=I' ∇=∇' Δ=Δ' = ∪ᵥ-cong (minusᵥ-cong I=I' (Γ₂,ᵢ-cong ∇=∇')) (Γ₂,ᵢ-cong Δ=Δ')

Γ₃,ₒ-cong : ∀ {V V'} → V ≈ᵥ V' → Γ₃,ₒ V ≈ᵥ,₂ Γ₃,ₒ V'
Γ₃,ₒ-cong = Γ₂,ₒ-cong

Γ₃,ₓ-cong : ∀ {V V' O O'} → V ≈ᵥ V' → O ≈ᵥ,₂ O' →
            (π₁ (Γ₃,ₓ V O) ≈ᵥ,₂ π₁(Γ₃,ₓ V' O')) ×
            (π₂ (Γ₃,ₓ V O) ≈ᵥ,₂ π₂(Γ₃,ₓ V' O'))
Γ₃,ₓ-cong V=V' O=O' = diffᵥ-cong O=O' (Γ₃,ₒ-cong V=V')

Γ₃-cong : ∀ {S S'} → S ≈ₛ S' → Γ₃ S ≈ₛ Γ₃ S'
Γ₃-cong (V=V' , I=I' , O=O' , ∇=∇' , Δ=Δ') = 
  Γ₃,ᵥ-cong I=I' ,
  Γ₃,ᵢ-cong I=I' ∇=∇' Δ=Δ' ,
  Γ₃,ₒ-cong V=V' ,
  π₁ (Γ₃,ₓ-cong V=V' O=O') ,
  π₂ (Γ₃,ₓ-cong V=V' O=O')

------------------------------------
-- Theorems

postulate
  -- Lemma A.5
  F-union-cong : ∀ {i j} → (f : Step i j) → (A B : RoutingSet)
                 → f [ A ∪ B ] ↭ f [ A ] ∪ f [ B ]
  -- Lemma A.6
  F-minus-cong : ∀ {i j} → (f : Step i j) → (A B : RoutingSet)
               → f [ A - B ] ↭ f [ A ] - f [ B ]
  diff-lemma : ∀ A B → let (∇ , Δ) = diff A B in
          (A - ∇) ∪ Δ ↭ B

-- Lemma 3.3
F-diff-cong : ∀ F A B → let (∇ , Δ) = diffᵥ A B in
              ((F 〖 A 〗 -ᵥ F 〖 ∇ 〗) ∪ᵥ F 〖 Δ 〗) ≈ᵥ,₂ (F 〖 B 〗)
F-diff-cong F A B i j = let (∇ , Δ) = diffᵥ A B in begin
  ((F 〖 A 〗 -ᵥ F 〖 ∇ 〗) ∪ᵥ F 〖 Δ 〗) i j ↭⟨ ↭-refl ⟩
  ((F i j) [ A j i ] - (F i j) [ ∇ j i ]) ∪ (F i j) [ Δ j i ]
    ↭⟨ ∪-cong {A = ((F i j) [ A j i ] - (F i j) [ ∇ j i ])}
              {A' = ((F i j) [ (A j i) - (∇ j i) ])}
              {B = (F i j) [ Δ j i ]}
              (↭-sym (F-minus-cong (F i j) (A j i) (∇ j i))) ↭-refl ⟩
  ((F i j) [ ((A j i) - (∇ j i)) ]) ∪ (F i j) [ Δ j i ]
    ↭⟨ ↭-sym (F-union-cong (F i j) ((A j i) - (∇ j i)) (Δ j i)) ⟩
  (F i j) [  ((A j i) - (∇ j i)) ∪ (Δ j i) ] ↭⟨ []-cong (diff-lemma (A j i) (B j i)) ⟩
  (F 〖 B 〗) i j ∎
  where open PermutationReasoning

-- postulate
  -- -- Theorem 8
  -- Γ₁=Γ₃ : ∀ {k} → let I' = (Γ₂,ᵢ ∘ Γ₂,ₒ) ((Γ₁ ^ k) (~ M))
  --                     O' = Γ₂,ₒ ((Γ₁ ^ k) (~ M)) in
  --         (Γ₃-Model ^ (3 * (suc k))) (S₃ (~ M) Øᵥ,₂ Øᵥ,₂ (Øᵥ,₂ , Øᵥ,₂)) ≈ₛ
  --         S₃ ((Γ₁ ^ (suc k)) (~ M)) I' O' (Øᵥ,₂ , Øᵥ,₂)

-- tgg: we made some mistakes regarding Γ₃ !

-- To fix, we simply need an invariant, so that we can equate each step of Γ₃ with a step of Γ₂.
-- We only need to ensure that at each step the I component of Γ₃ is equal to the I component of Γ₂.
-- Then the V, I, and O components will be the same at each step. 

Γ₃-invariant : Γ₃-State → Set (a ⊔ ℓ)
Γ₃-invariant (S₃ V I O (∇ , Δ)) = Γ₂,ᵢ O ≈ᵥ,₂ Γ₃,ᵢ I  (∇ , Δ)

Γ₃-invariant-maintained : ∀ (S : Γ₃-State) → Γ₃-invariant S → Γ₃-invariant (Γ₃ S) 
Γ₃-invariant-maintained (S₃ V I O (∇ , Δ)) inv = {!!} 
-- 
-- hand proof: 
-- let 
--  Γ₃ (S₃ V I O (∇ , Δ)) = (S₃ V' I' O' (∇' , Δ'))
--
--  Need to show Γ₂,ᵢ O' ≈ᵥ,₂ Γ₃,ᵢ I'  (∇' , Δ')
--  That is,
--  Γ₂,ᵢ (Γ₂,ₒ V) ≈ᵥ,₂ Γ₃,ᵢ (Γ₃,ᵢ I  (∇ , Δ))  diffᵥ O (Γ₃,ₒ V)
--

-- proof:
--
-- Γ₃,ᵢ (Γ₃,ᵢ I  (∇ , Δ))  diffᵥ O (Γ₃,ₒ V)
-- = by invariant 
-- Γ₃,ᵢ (Γ₂,ᵢ O)  diffᵥ O (Γ₃,ₒ V)
-- =
-- Γ₃,ᵢ (Γ₂,ᵢ O)  (O - (Γ₃,ₒ V), (Γ₃,ₒ V) - O) 
-- =
-- ((Γ₂,ᵢ O) - (Γ₂,ᵢ (O - (Γ₃,ₒ V)))) ∪ (Γ₂,ᵢ ((Γ₃,ₒ V) - O))
-- = by magic ;-) 
-- Γ₂,ᵢ (O - (O - (Γ₃,ₒ V)) ∪ ((Γ₃,ₒ V) - O))
-- = by algebra 
-- Γ₂,ᵢ (Γ₂,ₒ V)

-- 

