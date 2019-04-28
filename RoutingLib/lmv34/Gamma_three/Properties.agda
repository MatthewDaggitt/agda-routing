open import Algebra.FunctionProperties.Core using (Op₂)
open import Data.Fin using (Fin)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.List using (List; filter; tabulate; []; _∷_; _++_; map)
import Data.List.Membership.DecSetoid as Membership
open import Data.Nat using (zero; suc; ℕ; _*_; _+_)
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
minus-cong A=A' B=B' = {!!}

∪-cong : ∀ {A A' B B'} → A ↭ A' → B ↭ B' →
         A ∪ B ↭ A' ∪ B'
∪-cong {A} {A'} {B} {B'} A=A' B=B' = ++-cong A=A' (minus-cong B=B' A=A')

[]-xs : ∀ xs → [] - xs ↭ []
[]-xs xs = ↭-refl

xs-[] : ∀ xs → xs - [] ↭ xs
xs-[] [] = ↭-refl
xs-[] (x ∷ xs) = prep ≈ᵣ-refl (xs-[] xs)

minus-cancellation : ∀ xs → xs - xs ↭ []
minus-cancellation [] = ↭-refl
minus-cancellation (y ∷ xs) with y ≟ᵣ y
... | no ¬p  = contradiction ≈ᵣ-refl ¬p
... | yes _ = ↭-trans (lemma y xs) (minus-cancellation xs)
  where lemma : ∀ y xs → xs - (y ∷ xs) ↭ xs - xs
        lemma y [] = ↭-refl
        lemma y (x ∷ xs) = {!!}

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
F-union-cong = {!!}

-- Lemma A.6
F-minus-cong : ∀ {i j} → (f : Step i j) → (A B : RoutingSet)
               → f [ A - B ] ↭ f [ A ] - f [ B ]
F-minus-cong = {!!}

-- Lemma 3.3
F-diff-cong : ∀ F A B → ((F 〖 A 〗 -ᵥ F 〖 proj₁ (diffᵥ A B) 〗) ∪ᵥ F 〖 proj₂ (diffᵥ A B) 〗) ≈ᵥ,₂ (F 〖 B 〗)
F-diff-cong F A B i j = begin
  ((F 〖 A 〗 -ᵥ F 〖 proj₁ (diffᵥ A B) 〗) ∪ᵥ F 〖 proj₂ (diffᵥ A B) 〗) i j ↭⟨ ↭-refl ⟩
  ((F i j) [ A j i ] - (F i j) [ (A j i) - (B j i) ]) ∪ (F i j) [ (B j i) - (A j i)] ↭⟨ ∪-cong (↭-sym (F-minus-cong (F i j) (A j i) ((A j i) - (B j i)))) ↭-refl ⟩
  ((F i j) [ ((A j i) - ((A j i) - (B j i))) ]) ∪ (F i j) [ (B j i) - (A j i)] ↭⟨ {!!} ⟩
  (F 〖 B 〗) i j ∎
  where open PermutationReasoning
  
