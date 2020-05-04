open import Algebra.Definitions
open import Data.Fin using (zero; suc; Fin)
open import Data.Fin.Subset using (Subset; ⊤; ⊥; _∈_)
open import Data.Fin.Subset.Properties using (_∈?_; ∉⊥; ∈⊤)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _≤_;  _<_; _∸_)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Data.Nat.Properties as ℕₚ using (≤-step; n≤1+n; m∸n≤m; ≤-refl; ≤-trans)
import Data.List.Relation.Binary.Permutation.Setoid as PermutationEq
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec.Functional.Relation.Binary.Pointwise.Properties using () renaming (decSetoid to decSetoidᵥ)
open import Function using (const; id; _∘_)
open import Level using (0ℓ; _⊔_)
open import Relation.Binary using (Rel; Decidable; DecSetoid; Setoid)
open import Relation.Binary.Indexed.Homogeneous using (Reflexive; Symmetric; Transitive; IRel; IsIndexedEquivalence; IsIndexedDecEquivalence; IndexedDecSetoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Relation.Binary.Reasoning.Setoid as EqReasoning
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

import RoutingLib.Data.List.Relation.Binary.Permutation.Setoid.Properties as PermutationProperties
open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
open import RoutingLib.Routing as Routing using (AdjacencyMatrix)
import RoutingLib.lmv34.Gamma_zero as Gamma_zero
import RoutingLib.lmv34.Gamma_zero.Algebra as Gamma_zero_Algebra
import RoutingLib.lmv34.Gamma_zero.Properties as Gamma_zero_Properties
import RoutingLib.lmv34.Gamma_one as Gamma_one
import RoutingLib.lmv34.Gamma_one.Algebra as Gamma_one_Algebra
import RoutingLib.lmv34.Gamma_one.Properties as Gamma_one_Properties
import RoutingLib.lmv34.Gamma_two as Gamma_two
open import RoutingLib.lmv34.Gamma_two.Algebra as Gamma_two_Algebra using (IsComposition) renaming (RouteMapMatrix to RouteMapMatrix')
import RoutingLib.lmv34.Gamma_two.Properties as Gamma_two_Properties
import RoutingLib.lmv34.Omega_zero as Omega_zero
import RoutingLib.lmv34.Omega_one as Omega_one
open import RoutingLib.Iteration.Synchronous using (_^_)
open import RoutingLib.Iteration.Asynchronous.Static using (AsyncIterable; asyncIter; asyncIter')
open import RoutingLib.Iteration.Asynchronous.Static.Schedule using (Schedule; 𝕋)
open import RoutingLib.Iteration.Asynchronous.Static.Schedule.Construct.Infinite using (ψ∞; α∞; β∞)
open import RoutingLib.Iteration.Asynchronous.Static.Schedule.Construct.Synchronous using (αˢʸⁿᶜ; βˢʸⁿᶜ; βˢʸⁿᶜ-causality; ψˢʸⁿᶜ; ψˢʸⁿᶜ-isSynchronous)
open import RoutingLib.Relation.Binary.Indexed.Homogeneous

module RoutingLib.lmv34.Omega_two
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra) {n}
  (A    : AdjacencyMatrix algebra n)
  (Imp Prot Exp : RouteMapMatrix' isRoutingAlgebra n )
  (A=Imp∘Prot∘Exp : IsComposition isRoutingAlgebra n A Imp Prot Exp)
  where

open Routing algebra n renaming (_≈ₘ_ to infix 3 _≈ₘ_; I to M) hiding (≈ₛ-refl; ≈ₛ-sym; ≈ₛ-trans)
open RawRoutingAlgebra algebra using (≈-refl) renaming (S to 𝕊)
open Gamma_zero_Algebra algebra n using (_⊕ₘ_; _〔_〕)
open Gamma_one isRoutingAlgebra A using (Γ₁)
open Gamma_one_Algebra isRoutingAlgebra n using (RoutingSet; RoutingVector; Øᵥ; _≈ᵥ_; ≈ᵥ-refl; ≈ᵥ-sym; ≈ᵥ-trans; _⊕ᵥ_; ⨁ₛ; ~_; ─_; _[_]; _〚_〛; FinRoute-setoid; FinRoute-decSetoid; 𝕍ₛ)
open Gamma_one_Properties isRoutingAlgebra A using (Γ₁-cong; ⊕-distributive; ⊕ᵥ-cong; Lemma-Γ₀=Γ₁; 〚〛-cong; ⨁ₛ-cong; ⊕ₛ-cong; ≈ₘ⇒≈ᵥ)
open Gamma_two isRoutingAlgebra Imp Prot Exp using (Γ₂; Γ₂,ᵥ; Γ₂,ᵢ; Γ₂,ₒ)
open Gamma_two_Algebra isRoutingAlgebra n using (RoutingVector₂; RouteMapMatrix; toRouteMapMatrix; Øᵥ,₂; _≈ₐ,₂_; _〖_〗; _↓; _●_; _●ₘ_; _ᵀ)
open Gamma_two_Properties isRoutingAlgebra A Imp Prot Exp A=Imp∘Prot∘Exp using (Γ₁=Γ₂-comp; Γ₂-State-decSetoid; Γ₂,ᵥ-cong; Γ₂,ᵢ-cong; Γ₂,ₒ-cong; ≈ᵥ,₂-decSetoid; LemmaA₃; f[]-cong)
open Omega_zero algebra A using (Ω₀; [_,_]_; [,]-⊤; [,]-⊥)
open Omega_one isRoutingAlgebra A using (Γ₁'; Γ₁∥; Ω₁'; Ω₁; _⟦_⟧'; Γ₁-cong')
open PermutationEq FinRoute-setoid
open PermutationProperties FinRoute-setoid using (_↭?_; ↭-decSetoid)
open DecSetoid FinRoute-decSetoid using () renaming (_≟_ to _≟ᵣ_; refl to ≈ᵣ-refl)
open DecSetoid Γ₂-State-decSetoid using () renaming ( _≈_  to _≈ₛ_ ; refl to ≈ₛ-refl)
open DecSetoid ≈ᵥ,₂-decSetoid using () renaming (_≈_ to _≈ᵥ,₂_; refl to ≈ᵥ,₂-refl; setoid to 𝕍₂ₛ)

-- THIS PROOF IS WORK-IN-PROGRESS

--------------------------------------------------------------------------------
-- Various proofs and statements
-- TODO: reorganise the lmv34 folder, split into Algebra/Properties files.

-- State = (V , I , O)
Γ₂-State : Set a
Γ₂-State = RoutingVector × RoutingVector₂ × RoutingVector₂

-- Generalised export function application
infix 10 _【_】'
_【_】' : RouteMapMatrix → (Fin n → Fin n → RoutingSet) → RoutingVector₂
(F 【 f 】') i q = (F i q) [ f q i ]

-- Generalised (asynchronous) operator
Γ₂,ₒ' : (Fin n → Fin n → RoutingSet) → RoutingVector₂
Γ₂,ₒ' f = Exp 【 f 】'

infix 10 _||_||'
_||_||' : RouteMapMatrix → (Fin n → RoutingVector) → RoutingVector
(A || V ||' ) i = ⨁ₛ (λ q → (A i q) [ V i q ])

⟦⟧=||' : ∀ {A V} → A ⟦ V ⟧' ≈ᵥ (toRouteMapMatrix A) || V ||'
⟦⟧=||' = ≈ᵥ-refl

A||V||-cong' : ∀ {F F' V} → F ≈ₐ,₂ F' → F || V ||' ≈ᵥ  F' || V ||'
A||V||-cong' {F} {F'} {V} F=F' i = ⨁ₛ-cong (λ {q} → f[]-cong {X = V i q} (F=F' i q))

LemmaA₄' : ∀ F G V → (F 〖 (G 【 V 】') 〗) ↓ ≈ᵥ (F ●ₘ (G ᵀ)) || V ||'
LemmaA₄' F G V i = begin
   ((F 〖 G 【 V 】' 〗) ↓) i ↭⟨ ↭-refl ⟩
   ⨁ₛ (λ q → (F i q) [ (G q i) [ V i q ] ]) ↭⟨ ⨁ₛ-cong (λ {q} → (LemmaA₃ (F i q) (G q i) (V i q))) ⟩
   ⨁ₛ (λ q → ((F i q) ● (G q i)) [ V i q ]) ↭⟨ ↭-refl ⟩
   ((F ●ₘ (G ᵀ)) || V ||') i ∎
   where open PermutationReasoning

-- Generalised (asynchronous) cycle property
Γ₁=Γ₂-comp' : ∀ (V : Fin n → RoutingVector) → Γ₁' V ≈ᵥ (Γ₂,ᵥ ∘ Γ₂,ᵢ ∘ Γ₂,ₒ') V
Γ₁=Γ₂-comp' V = begin
  Γ₁' V                                         ≈⟨ ≈ᵥ-refl ⟩
  (A ⟦ V ⟧') ⊕ᵥ ~ M                              ≈⟨ ⊕ᵥ-cong (⟦⟧=||' {A} {V}) (≈ₘ⇒≈ᵥ ≈ₘ-refl) ⟩ 
  (toRouteMapMatrix A) || V ||'  ⊕ᵥ ~ M      ≈⟨ ⊕ᵥ-cong (A||V||-cong' {V = V} A=Imp∘Prot∘Exp) (≈ₘ⇒≈ᵥ ≈ₘ-refl) ⟩
  ((Imp ●ₘ Prot) ●ₘ (Exp ᵀ)) || V ||' ⊕ᵥ ~ M    ≈⟨ ⊕ᵥ-cong (≈ᵥ-sym (LemmaA₄' (Imp ●ₘ Prot) Exp V)) (≈ₘ⇒≈ᵥ ≈ₘ-refl)   ⟩ 
  ((Imp ●ₘ Prot) 〖 Exp 【 V 】' 〗) ↓ ⊕ᵥ ~ M    ≈⟨ ≈ᵥ-refl ⟩
  (Γ₂,ᵥ ∘ Γ₂,ᵢ ∘ Γ₂,ₒ') V                        ∎
  where open EqReasoning 𝕍ₛ

[_,_]-cong : ∀ {X X' Y Y' : RoutingVector} (S : Subset n) →
             X ≈ᵥ X' → Y ≈ᵥ Y' → [ X , Y ] S ≈ᵥ [ X' , Y' ] S
[_,_]-cong S X=X' Y=Y' i with i ∈? S
... | yes _ = X=X' i
... | no  _ = Y=Y' i

getV : Γ₂-State → RoutingVector
getV (V , I , O) = V

getI : Γ₂-State → RoutingVector₂
getI (V , I , O) = I

getO : Γ₂-State → RoutingVector₂
getO (V , I , O) = O

getV=V' : ∀ {S S'} → S ≈ₛ S' → getV S ≈ᵥ getV S'
getV=V' (V=V' , I=I' , O=O') = V=V'

getI=I' : ∀ {S S'} → S ≈ₛ S' → getI S ≈ᵥ,₂ getI S'
getI=I' (V=V' , I=I' , O=O') = I=I'

getO=O' : ∀ {S S'} → S ≈ₛ S' → getO S ≈ᵥ,₂ getO S'
getO=O' (V=V' , I=I' , O=O') = O=O'

--------------------------------------------------------------------------------
-- Implementation of Ω₂

-- A triple schedule, one for each component V, I, O
Schedule₃ : ℕ → Set
Schedule₃ n = (Schedule n) × (Schedule n) × (Schedule n)

ψ₃ˢʸⁿᶜ : Schedule₃ n
ψ₃ˢʸⁿᶜ = (ψˢʸⁿᶜ , ψˢʸⁿᶜ , ψˢʸⁿᶜ)

module _ ((ψᵥ , ψᵢ , ψₒ) : Schedule₃ n) where
  open Schedule ψᵥ renaming (α to αᵥ; β to βᵥ; β-causality to βᵥ-causality)
  open Schedule ψᵢ renaming (α to αᵢ; β to βᵢ; β-causality to βᵢ-causality)
  open Schedule ψₒ renaming (α to αₒ; β to βₒ; β-causality to βₒ-causality)
  
  Ω₂' : Γ₂-State → {t : 𝕋} → Acc _<_ t → Γ₂-State
  Ω₂' S {zero}  accₜ      = S
  Ω₂' S {suc t} (acc rec) =
    ( [ Γ₂,ᵥ Iᵇ⁽ᵗ⁺¹⁾ , Vᵗ ] αᵥ (suc t)
    , [ Γ₂,ᵢ Oᵇ⁽ᵗ⁺¹⁾ , Iᵗ ] αᵢ (suc t)
    , [ Γ₂,ₒ Vᵇ⁽ᵗ⁺̂¹⁾ , Oᵗ ] αₒ (suc t)
    )
    where Vᵗ : RoutingVector
          Vᵗ = getV (Ω₂' S (rec t ≤-refl))
          Vᵇ⁽ᵗ⁺̂¹⁾ : RoutingVector
          Vᵇ⁽ᵗ⁺̂¹⁾ i = (getV (Ω₂' S (rec (βₒ (suc t) i i) (s≤s (βₒ-causality t i i))))) i
          Iᵗ : RoutingVector₂
          Iᵗ = getI (Ω₂' S (rec t ≤-refl))
          Iᵇ⁽ᵗ⁺¹⁾ : RoutingVector₂
          Iᵇ⁽ᵗ⁺¹⁾ i j = (getI (Ω₂' S (rec (βᵥ (suc t) i i) (s≤s (βᵥ-causality t i i))))) i j
          Oᵗ : RoutingVector₂
          Oᵗ = getO (Ω₂' S (rec t ≤-refl))
          Oᵇ⁽ᵗ⁺¹⁾ : RoutingVector₂
          Oᵇ⁽ᵗ⁺¹⁾ i j = (getO (Ω₂' S (rec (βᵢ (suc t) j i) (s≤s (βᵢ-causality t j i))))) i j

Ω₂ : Schedule₃ n → Γ₂-State → 𝕋 → Γ₂-State
Ω₂ ψ S t = Ω₂' ψ S (<-wellFounded t)

--------------------------------------------------------------------------------
-- Proof that synchronous Ω₂ is indeed Γ₂

Ω₂'ˢʸⁿᶜ=Γ₂ : ∀ S {t} (accₜ : Acc _<_ t) → Ω₂' ψ₃ˢʸⁿᶜ S accₜ ≈ₛ (Γ₂ ^ t) S
Ω₂'ˢʸⁿᶜ=Γ₂ S {zero}  accₜ      = ≈ₛ-refl
Ω₂'ˢʸⁿᶜ=Γ₂ S {suc t} (acc rec) = (V=V' , I=I' , O=O')
  where Ω₂-Vᵗ⁺¹ : RoutingVector
        Ω₂-Vᵗ⁺¹ = getV (Ω₂' ψ₃ˢʸⁿᶜ S (acc rec))
        Γ₂-Vᵗ⁺¹ : RoutingVector
        Γ₂-Vᵗ⁺¹ = getV ((Γ₂ ^ (suc t)) S)
        Ω₂-Iᵗ⁺¹ : RoutingVector₂
        Ω₂-Iᵗ⁺¹ = getI (Ω₂' ψ₃ˢʸⁿᶜ S (acc rec))
        Γ₂-Iᵗ⁺¹ : RoutingVector₂
        Γ₂-Iᵗ⁺¹ = getI ((Γ₂ ^ (suc t)) S)
        Ω₂-Oᵗ⁺¹ : RoutingVector₂
        Ω₂-Oᵗ⁺¹ = getO (Ω₂' ψ₃ˢʸⁿᶜ S (acc rec))
        Γ₂-Oᵗ⁺¹ : RoutingVector₂
        Γ₂-Oᵗ⁺¹ = getO ((Γ₂ ^ (suc t)) S)
        Vᵗ : RoutingVector
        Vᵗ = getV (Ω₂' ψ₃ˢʸⁿᶜ S (rec t ≤-refl))
        Vᵇ⁽ᵗ⁺̂¹⁾ : RoutingVector
        Vᵇ⁽ᵗ⁺̂¹⁾ i = (getV (Ω₂' ψ₃ˢʸⁿᶜ S (rec (βˢʸⁿᶜ (suc t) i i) (s≤s (βˢʸⁿᶜ-causality t i i))))) i
        Iᵗ : RoutingVector₂
        Iᵗ = getI (Ω₂' ψ₃ˢʸⁿᶜ S (rec t ≤-refl))
        Iᵇ⁽ᵗ⁺¹⁾ : RoutingVector₂
        Iᵇ⁽ᵗ⁺¹⁾ i j = (getI (Ω₂' ψ₃ˢʸⁿᶜ S (rec (βˢʸⁿᶜ (suc t) i i) (s≤s (βˢʸⁿᶜ-causality t i i))))) i j
        Oᵗ : RoutingVector₂
        Oᵗ = getO (Ω₂' ψ₃ˢʸⁿᶜ S (rec t ≤-refl))
        Oᵇ⁽ᵗ⁺¹⁾ : RoutingVector₂
        Oᵇ⁽ᵗ⁺¹⁾ i j = (getO (Ω₂' ψ₃ˢʸⁿᶜ S (rec (βˢʸⁿᶜ (suc t) j i) (s≤s (βˢʸⁿᶜ-causality t j i))))) i j

        V=V' : Ω₂-Vᵗ⁺¹ ≈ᵥ Γ₂-Vᵗ⁺¹
        V=V' = begin
          Ω₂-Vᵗ⁺¹                              ≡⟨⟩
          [ Γ₂,ᵥ Iᵇ⁽ᵗ⁺¹⁾ , Vᵗ ] αˢʸⁿᶜ (suc t)   ≡⟨ [,]-⊤ (Γ₂,ᵥ Iᵇ⁽ᵗ⁺¹⁾) Vᵗ ⟩
          Γ₂,ᵥ Iᵇ⁽ᵗ⁺¹⁾                         ≡⟨⟩
          Γ₂,ᵥ Iᵗ                              ≈⟨ Γ₂,ᵥ-cong (getI=I' (Ω₂'ˢʸⁿᶜ=Γ₂ S (rec t ≤-refl))) ⟩
          Γ₂-Vᵗ⁺¹                              ∎
          where open EqReasoning 𝕍ₛ

        I=I' : Ω₂-Iᵗ⁺¹ ≈ᵥ,₂ Γ₂-Iᵗ⁺¹
        I=I' = begin
          Ω₂-Iᵗ⁺¹                              ≡⟨⟩
          [ Γ₂,ᵢ Oᵇ⁽ᵗ⁺¹⁾ , Iᵗ ] αˢʸⁿᶜ (suc t)   ≡⟨ [,]-⊤ (Γ₂,ᵢ Oᵇ⁽ᵗ⁺¹⁾) Iᵗ ⟩
          Γ₂,ᵢ Oᵇ⁽ᵗ⁺¹⁾                         ≡⟨⟩
          Γ₂,ᵢ Oᵗ                              ≈⟨ Γ₂,ᵢ-cong (getO=O' (Ω₂'ˢʸⁿᶜ=Γ₂ S (rec t ≤-refl))) ⟩
          Γ₂-Iᵗ⁺¹                              ∎
          where open EqReasoning 𝕍₂ₛ

        O=O' : Ω₂-Oᵗ⁺¹ ≈ᵥ,₂ Γ₂-Oᵗ⁺¹
        O=O' = begin
          Ω₂-Oᵗ⁺¹                              ≡⟨⟩
          [ Γ₂,ₒ Vᵇ⁽ᵗ⁺̂¹⁾ , Oᵗ ] αˢʸⁿᶜ (suc t)   ≡⟨ [,]-⊤ (Γ₂,ₒ Vᵇ⁽ᵗ⁺̂¹⁾) Oᵗ ⟩
          Γ₂,ₒ Vᵇ⁽ᵗ⁺̂¹⁾                         ≡⟨⟩
          Γ₂,ₒ Vᵗ                              ≈⟨ Γ₂,ₒ-cong (getV=V' (Ω₂'ˢʸⁿᶜ=Γ₂ S (rec t ≤-refl))) ⟩
          Γ₂-Oᵗ⁺¹                              ∎
          where open EqReasoning 𝕍₂ₛ

Ω₂ˢʸⁿᶜ=Γ₂ : ∀ S t → Ω₂ ψ₃ˢʸⁿᶜ S t ≈ₛ (Γ₂ ^ t) S
Ω₂ˢʸⁿᶜ=Γ₂ S t = Ω₂'ˢʸⁿᶜ=Γ₂ S (<-wellFounded t)

--------------------------------------------------------------------------------
-- Reduction/transformation Ω₂ → Ω₁

-- The function ϕ find the timestamp of the most recent data from node j
-- that is being used at node i.
module _ {n} (ψ : Schedule n) where
  open Schedule ψ
  
  ϕ : 𝕋 → Fin n → Fin n → 𝕋
  ϕ zero    i j = zero
  ϕ (suc t) i j with i ∈? α (suc t)
  ... | yes _ = β (suc t) i j
  ... | no  _ = ϕ t i j

  ϕ-causality : ∀ t i j → ϕ (suc t) i j ≤ t
  ϕ-causality zero    i j with i ∈? α (suc zero)
  ... | yes _ = β-causality zero i j
  ... | no  _ = ≤-refl
  ϕ-causality (suc t) i j with i ∈? α (suc (suc t))
  ... | yes _ = β-causality (suc t) i j
  ... | no  _ = ≤-step (ϕ-causality t i j)

  ϕ-decreasing : ∀ t i j → ϕ t i j ≤ t
  ϕ-decreasing zero    i j = ≤-refl
  ϕ-decreasing (suc t) i j = ≤-step (ϕ-causality t i j)

  ϕ-strictly-decreasing : ∀ t i j → 1 ≤ t → ϕ t i j < t
  ϕ-strictly-decreasing (suc t) i j 1≤t = s≤s (ϕ-causality t i j)

  ϕ-≤-decreasing : ∀ t t' i j → t ≤ t' → ϕ t i j ≤ t'
  ϕ-≤-decreasing t t' i j t≤t' = ≤-trans (ϕ-decreasing t i j) t≤t'

ϕ-synchronous : ∀ {n} t i j → ϕ (ψˢʸⁿᶜ {n}) t i j ≡ t ∸ 1
ϕ-synchronous zero i j = refl
ϕ-synchronous (suc t) i j with i ∈? αˢʸⁿᶜ (suc t)
... | yes _       = refl
... | no  i∉αˢʸⁿᶜ = contradiction ∈⊤ i∉αˢʸⁿᶜ

ϕ-asynchronous : ∀ {n} t i j → ϕ (ψ∞ {n}) t i j ≡ 0
ϕ-asynchronous zero i j = refl
ϕ-asynchronous (suc t) i j with i ∈? α∞ (suc t)
... | yes i∈α∞ = contradiction i∈α∞ ∉⊥
... | no  _    = ϕ-asynchronous t i j

-- The function follow-cycle finds the timestamp of the most recent
-- data from the routing table V of node j, that is being used at
-- node i. It follows the cycle that of data flow in Ω₂.

module _ {n} ((ψᵥ , ψᵢ , ψₒ) : Schedule₃ n) where
  tᵢ : 𝕋 → Fin n → 𝕋
  tᵢ t i = ϕ ψᵥ t i i

  tₒ : 𝕋 → Fin n → Fin n → 𝕋
  tₒ t i j = ϕ ψᵢ (tᵢ t i) i j

  tᵥ : 𝕋 → Fin n → Fin n → 𝕋
  tᵥ t i j = ϕ ψₒ (tₒ t i j) j j

  tᵢ≤t : ∀ t i → tᵢ (suc t) i ≤ t
  tᵢ≤t t i = ϕ-causality ψᵥ t i i

  tₒ≤t : ∀ t i j → tₒ (suc t) i j ≤ t
  tₒ≤t t i j = ≤-trans (ϕ-decreasing ψᵢ (tᵢ (suc t) i) i j) (tᵢ≤t t i) 

  tᵥ≤t : ∀ t i j → tᵥ (suc t) i j ≤ t
  tᵥ≤t t i j = ≤-trans (ϕ-decreasing ψₒ (tₒ (suc t) i j) j j) (tₒ≤t t i j)

follow-cycle : ∀ {n} → Schedule₃ n → 𝕋 → Fin n → Fin n → 𝕋
follow-cycle ψ = tᵥ ψ

follow-cycle-causality : ∀ {n} (ψ : Schedule₃ n) t i j → follow-cycle ψ (suc t) i j ≤ t
follow-cycle-causality = tᵥ≤t

follow-cycle-decreasing : ∀ {n} (ψ : Schedule₃ n) t i j → follow-cycle ψ t i j ≤ t
follow-cycle-decreasing ψ zero i j = ≤-refl
follow-cycle-decreasing ψ (suc t) i j = ≤-step (follow-cycle-causality ψ t i j)

follow-cycle-strictly-decreasing : ∀ {n} (ψ : Schedule₃ n) t i j → 1 ≤ t → follow-cycle ψ t i j < t
follow-cycle-strictly-decreasing ψ (suc t) i j 1≤t = s≤s (follow-cycle-causality ψ t i j)

-- Schedule reduction Ω₂ → Ω₁
r₂ : ∀ {n} → Schedule₃ n → Schedule n
r₂ {n} (ψᵥ , ψᵢ , ψₒ) = record { α = α' ; β = β' ; β-causality = β'-causality}
  where open Schedule ψᵥ using () renaming (α to αᵥ)
        α' : 𝕋 → Subset n
        α' = αᵥ
        β' : 𝕋 → Fin n → Fin n → 𝕋
        β' = follow-cycle (ψᵥ , ψᵢ , ψₒ)
        β'-causality : ∀ t i j → β' (suc t) i j ≤ t
        β'-causality = follow-cycle-causality (ψᵥ , ψᵢ , ψₒ)

-- Transformation Ω₂ → Ω₁
Τ₂ : Γ₂-State → RoutingVector
Τ₂ (V , I , O) = V

--------------------------------------------------------------------------------
-- Proof of Ω₂=Ω₁

S₀ : Γ₂-State
S₀ = (Øᵥ , Øᵥ,₂ , Øᵥ,₂)

module _ ((ψᵥ , ψᵢ , ψₒ) : Schedule₃ n)  where
  ψ : Schedule₃ n
  ψ = (ψᵥ , ψᵢ , ψₒ)
  
  open Schedule ψᵥ using () renaming (α to αᵥ; β to βᵥ; β-causality to βᵥ-causality)
  open Schedule ψᵢ using () renaming (α to αᵢ; β to βᵢ; β-causality to βᵢ-causality)
  open Schedule (r₂ ψ) using () renaming (α to α'; β to β'; β-causality to β'-causality)

  -- Lemmas
  pred : ∀ {t} → Acc _<_ (suc t) → Acc _<_ t
  pred {t} (acc rec) = rec t ≤-refl

  acc[tᵢ] : ∀ {t} {i} → Acc _<_ (suc t) → Acc _<_ (tᵢ ψ (suc t) i)
  acc[tᵢ] {t} {i} (acc rec) = rec (tᵢ ψ (suc t) i) (s≤s (tᵢ≤t ψ t i))

  acc[tₒ] : ∀ {t} {q} {i} → Acc _<_ (suc t) → Acc _<_ (tₒ ψ (suc t) q i)
  acc[tₒ] {t} {q} {i} (acc rec) = rec (tₒ ψ (suc t) q i) (s≤s (tₒ≤t ψ t q i))

  acc[tᵥ] : ∀ {t} {i} {q} → Acc _<_ (suc t) → Acc _<_ (tᵥ ψ (suc t) i q)
  acc[tᵥ] {t} {i} {q} (acc rec) = rec (tᵥ ψ (suc t) i q) (s≤s (tᵥ≤t ψ t i q))

  acc[βᵥ] : ∀ {t} {i} → Acc _<_ (suc t) → Acc _<_ (βᵥ (suc t) i i)
  acc[βᵥ] {t} {i} (acc rec) = rec (βᵥ (suc t) i i) (s≤s (βᵥ-causality t i i))

  acc[β'] : ∀ {t} {i} {q} → Acc _<_ (suc t) → Acc _<_ (β' (suc t) i q)
  acc[β'] {t} {i} {q} (acc rec) = rec (β' (suc t) i q) (s≤s (β'-causality t i q))

  lem : ∀ {t} {i} → i ∈ αᵥ (suc t) → βᵥ (suc t) i i ≡ tᵢ ψ (suc t) i
  lem {t} {i} i∈α with i ∈? αᵥ (suc t)
  ... | yes _ = refl
  ... | no i∉α = contradiction i∈α i∉α

  Ω₂'-cong : ∀ {t t'} {accₜ : Acc _<_ t} {accₜ' : Acc _<_ t'} →
             ∀ i → t ≡ t' → getI (Ω₂' ψ S₀ accₜ) i ≈ᵥ getI (Ω₂' ψ S₀ accₜ') i
  Ω₂'-cong = {!!}

  lem₁ : ∀ {t} (acc[t+1] : Acc _<_ (suc t)) →
         let V[t+1] = getV (Ω₂' ψ S₀ acc[t+1])
             V[t] = getV (Ω₂' ψ S₀ (pred acc[t+1]))
             I[tᵢ] = λ i q → getI (Ω₂' ψ S₀ (acc[tᵢ] {t} {i} acc[t+1])) i q in
         V[t+1] ≈ᵥ [ Γ₂,ᵥ I[tᵢ] , V[t] ] αᵥ (suc t)
  lem₁ {t} (acc rec) i with i ∈? αᵥ (suc t)
  ... | yes i∈α = ⊕ₛ-cong (⨁ₛ-cong λ {q} → prf q) (≈ₘ⇒≈ᵥ ≈ₘ-refl i)
    where V[t+1] : RoutingVector
          V[t+1] = getV (Ω₂' ψ S₀ (acc rec))
          I[tᵢ] : RoutingVector₂
          I[tᵢ] i q = getI (Ω₂' ψ S₀ (acc[tᵢ] {t} {i} (acc rec))) i q
          Iᵇ⁽ᵗ⁺¹⁾ : RoutingVector₂
          Iᵇ⁽ᵗ⁺¹⁾ i j = (getI (Ω₂' ψ S₀ (acc[βᵥ] {t} {i} (acc rec)))) i j
          prf : Iᵇ⁽ᵗ⁺¹⁾ i ≈ᵥ I[tᵢ] i
          prf = Ω₂'-cong i (lem {t} {i} i∈α)
  ... | no  _ = ↭-refl

  lem₂ : ∀ {t} (acc[t+1] : Acc _<_ (suc t)) →
         let I[tᵢ] = λ i q → getI (Ω₂' ψ S₀ (acc[tᵢ] {t} {i} acc[t+1])) i q
             O[tₒ] = λ i q → getO (Ω₂' ψ S₀ (acc[tₒ] {t} {q} {i} acc[t+1])) i q in
         I[tᵢ] ≈ᵥ,₂ Γ₂,ᵢ O[tₒ]
  lem₂ {t} (acc rec) i q = {!!}

  lem₃ : ∀ {t} (acc[t+1] : Acc _<_ (suc t)) →
         let O[tₒ] = λ i q → getO (Ω₂' ψ S₀ (acc[tₒ] {t} {q} {i} acc[t+1])) i q
             V[tᵥ] = λ i q → getV (Ω₂' ψ S₀ (acc[tᵥ] {t} {i} {q} acc[t+1])) q in
         O[tₒ] ≈ᵥ,₂ Γ₂,ₒ' V[tᵥ]
  lem₃ {t} (acc rec) i q = {!!}

  lem₄ : ∀ {t} (acc[t+1] : Acc _<_ (suc t)) →
         let V[t+1]  = getV (Ω₂' ψ S₀ acc[t+1])
             V[t]    = getV (Ω₂' ψ S₀ (pred acc[t+1]))
             V[tᵥ] = λ i q → getV (Ω₂' ψ S₀ (acc[tᵥ] {t} {i} {q} acc[t+1])) q in
         V[t+1] ≈ᵥ [ Γ₁' V[tᵥ] ,  V[t] ] αᵥ (suc t)
  lem₄ {t} acc[t+1] = begin
    V[t+1]                                         ≈⟨ lem₁ acc[t+1] ⟩
    [ Γ₂,ᵥ I[tᵢ] , V[t] ] αᵥ (suc t)                ≈⟨ [_,_]-cong (αᵥ (suc t)) (Γ₂,ᵥ-cong (lem₂ acc[t+1])) ≈ᵥ-refl ⟩
    [ Γ₂,ᵥ (Γ₂,ᵢ O[tₒ]) , V[t] ] αᵥ (suc t)         ≈⟨ [_,_]-cong (αᵥ (suc t)) (Γ₂,ᵥ-cong (Γ₂,ᵢ-cong (lem₃ acc[t+1]))) ≈ᵥ-refl ⟩
    [ Γ₂,ᵥ (Γ₂,ᵢ (Γ₂,ₒ' V[tᵥ])) , V[t] ] αᵥ (suc t) ≈⟨ [_,_]-cong (αᵥ (suc t)) (≈ᵥ-sym (Γ₁=Γ₂-comp' V[tᵥ])) ≈ᵥ-refl ⟩
    [ Γ₁' V[tᵥ] , V[t] ] αᵥ (suc t)       ∎
    where open EqReasoning 𝕍ₛ
          V[t+1] : RoutingVector
          V[t+1] = getV (Ω₂' ψ S₀ acc[t+1])
          V[t] : RoutingVector
          V[t] = getV (Ω₂' ψ S₀ (pred acc[t+1]))
          I[tᵢ] : RoutingVector₂
          I[tᵢ] i q = getI (Ω₂' ψ S₀ (acc[tᵢ] {t} {i} acc[t+1])) i q
          O[tₒ] : RoutingVector₂
          O[tₒ] i q = getO (Ω₂' ψ S₀ (acc[tₒ] {t} {q} {i} acc[t+1])) i q
          V[tᵥ] : Fin n → RoutingVector
          V[tᵥ] i q = getV (Ω₂' ψ S₀ (acc[tᵥ] {t} {i} {q} acc[t+1])) q

  Ω₂'=Ω₁' : ∀ {t} (acc[t] : Acc _<_ t) → Τ₂ (Ω₂' ψ S₀ acc[t]) ≈ᵥ Ω₁' (r₂ ψ) (Τ₂ S₀) acc[t]
  Ω₂'=Ω₁' {zero} _    = ≈ᵥ-refl
  Ω₂'=Ω₁' {suc t} (acc rec) = begin
    Τ₂ (Ω₂' ψ S₀ (acc rec))     ≡⟨⟩
    V₂[t+1]                    ≈⟨ lem₄ (acc rec) ⟩
    [ Γ₁' V₂[tᵥ] , V₂[t] ] αᵥ (suc t) ≈⟨ [_,_]-cong (αᵥ (suc t)) (Γ₁-cong' V₂[tᵥ]=V₁[tᵥ]) V₂[t]=V₁[t] ⟩
    [ Γ₁' V₁[tᵥ] , V₁[t] ] αᵥ (suc t) ≈⟨ [_,_]-cong (αᵥ (suc t)) (Γ₁-cong' V₁[tᵥ]=V₁[β']) ≈ᵥ-refl ⟩
    [ Γ₁' V₁[β'] , V₁[t] ] α' (suc t) ≈⟨ {!!} ⟩ -- re-implement Ω₁ to use the choice operator
    Ω₁' (r₂ ψ) (Τ₂ S₀) (acc rec) ∎
      where open EqReasoning 𝕍ₛ
            V₂[t+1] : RoutingVector
            V₂[t+1] = getV (Ω₂' ψ S₀ (acc rec))
            V₂[t] : RoutingVector
            V₂[t] = getV (Ω₂' ψ S₀ (pred (acc rec)))
            V₂[tᵥ] : Fin n → RoutingVector
            V₂[tᵥ] i q = getV (Ω₂' ψ S₀ (acc[tᵥ] {t} {i} {q} (acc rec))) q
            V₁[t+1] : RoutingVector
            V₁[t+1] = Ω₁' (r₂ ψ) (Τ₂ S₀) (acc rec)
            V₁[t] : RoutingVector
            V₁[t] = Ω₁' (r₂ ψ) (Τ₂ S₀) (pred (acc rec))
            V₁[tᵥ] : Fin n → RoutingVector
            V₁[tᵥ] i q = Ω₁' (r₂ ψ) (Τ₂ S₀) (acc[tᵥ] {t} {i} {q} (acc rec)) q
            V₁[β'] : Fin n → RoutingVector
            V₁[β'] i q = Ω₁' (r₂ ψ) (Τ₂ S₀) (acc[β'] {t} {i} {q} (acc rec)) q

            V₂[tᵥ]=V₁[tᵥ] : V₂[tᵥ] ≈ᵥ,₂ V₁[tᵥ]
            V₂[tᵥ]=V₁[tᵥ] i q = Ω₂'=Ω₁' (rec (tᵥ ψ (suc t) i q) (s≤s (tᵥ≤t ψ t i q))) q

            V₂[t]=V₁[t] : V₂[t] ≈ᵥ V₁[t]
            V₂[t]=V₁[t] = Ω₂'=Ω₁' (rec t ≤-refl)

            V₁[tᵥ]=V₁[β'] : V₁[tᵥ] ≈ᵥ,₂ V₁[β']
            V₁[tᵥ]=V₁[β'] = ≈ᵥ,₂-refl

Ω₂=Ω₁ : ∀ ψ t → Τ₂ (Ω₂ ψ S₀ t) ≈ᵥ Ω₁ (r₂ ψ) (Τ₂ S₀) t
Ω₂=Ω₁ ψ t = Ω₂'=Ω₁' ψ (<-wellFounded t)
