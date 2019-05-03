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
open Gamma_three isRAlg _●_ Imp Prot Exp
open Gamma_three_Algebra isRAlg n _●_

open DecSetoid FinRoute-decSetoid using () renaming (refl to ≈ᵣ-refl; _≟_ to _≟ᵣ_)
open Membership FinRoute-decSetoid using (_∈?_)

------------------------------------
-- Γ₃-State
infix 2 _≈ₛ_

_≈ₛ_ : Rel Γ₃-State (a ⊔ ℓ)
S ≈ₛ S' =
  Γ₃-State.V S ≈ᵥ Γ₃-State.V S'   ×
  Γ₃-State.O S ≈ᵥ,₂ Γ₃-State.O S' ×
  Γ₃-State.I S ≈ᵥ,₂ Γ₃-State.I S' ×
  π₁ (Γ₃-State.∇,Δ S) ≈ᵥ,₂ π₁ (Γ₃-State.∇,Δ S') ×
  π₂ (Γ₃-State.∇,Δ S) ≈ᵥ,₂ π₂ (Γ₃-State.∇,Δ S')

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

minus-cong : ∀ {A A' B B'} → A ↭ A' → B ↭ B' →
             A - B ↭ A' - B'
minus-cong {[]} {[]} A=A' B=B' = refl
minus-cong {x ∷ A} {.x ∷ .A} refl B=B' = {!!}
minus-cong {x ∷ A} {.(_ ∷ _)} (prep eq A=A') B=B' = {!!}
minus-cong {x ∷ .(_ ∷ _)} {.(_ ∷ _ ∷ _)} (swap eq₁ eq₂ A=A') B=B' = {!!}
minus-cong {A} {A'} (trans A=A' A'=A'') B=B' = trans (minus-cong A=A' refl) (minus-cong A'=A'' B=B')

∪-cong : ∀ {A A' B B'} → A ↭ A' → B ↭ B' →
         A ∪ B ↭ A' ∪ B'
∪-cong {A} {A'} {B} {B'} A=A' B=B' = ++-cong A=A' (minus-cong B=B' A=A')

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

------------------------------------
-- Theorems

-- Lemma A.5
F-union-cong : ∀ {i j} → (f : Step i j) → (A B : RoutingSet)
               → f [ A ∪ B ] ↭ f [ A ] ∪ f [ B ]
F-union-cong f [] B = begin
  f [ [] ∪ B ] ↭⟨ ↭-refl ⟩
  f [ B - [] ] ↭⟨ []-cong (xs-[] B)⟩
  f [ B ] ↭⟨ ↭-sym (xs-[] (f [ B ])) ⟩
  f [ [] ] ∪ f [ B ] ∎
  where open PermutationReasoning
F-union-cong f (x ∷ A) B = begin
  f [(x ∷ A) ∪ B ] ↭⟨ ↭-refl ⟩
  f [(x ∷ A) ++ (B - (x ∷ A))] ↭⟨ {!!} ⟩
  f [ x ∷ A ] ∪ f [ B ] ∎
  where open PermutationReasoning

-- Lemma A.6
F-minus-cong : ∀ {i j} → (f : Step i j) → (A B : RoutingSet)
               → f [ A - B ] ↭ f [ A ] - f [ B ]
F-minus-cong f [] B = ↭-refl
F-minus-cong f ((d , v) ∷ A) B with v ≟ ∞# | (d , v) ∈? B
... | yes _ | no _  = {!!}
... | yes _ | yes _ = {!!}
... | no _  | _ = {!!}

postulate
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

-- Theorem 8
Γ₁=Γ₃ : ∀ {k} → let I' = (Γ₂,ᵢ ∘ Γ₂,ₒ) ((Γ₁ ^ k) (~ M))
                    O' = Γ₂,ₒ ((Γ₁ ^ k) (~ M)) in
        (Γ₃-Model ^ (3 * (suc k))) (S₃ (~ M) Øᵥ,₂ Øᵥ,₂ (Øᵥ,₂ , Øᵥ,₂)) ≈ₛ
        S₃ ((Γ₁ ^ (suc k)) (~ M)) I' O' (Øᵥ,₂ , Øᵥ,₂)
Γ₁=Γ₃ {zero} = begin
  (Γ₃-Model ^ 3) (S₃ (~ M) Øᵥ,₂ Øᵥ,₂ (Øᵥ,₂ , Øᵥ,₂)) ≈⟨ {!!} ⟩
  S₃ (Γ₁ (~ M)) I' O' (Øᵥ,₂ , Øᵥ,₂) ∎
  where open EqReasoning 𝕊ₛ
        I' = (Γ₂,ᵢ ∘ Γ₂,ₒ) (~ M)
        O' = Γ₂,ₒ (~ M)
Γ₁=Γ₃ {suc k} = {!!}
