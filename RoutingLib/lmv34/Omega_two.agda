open import Algebra.Definitions
open import Data.Fin using (zero; suc; Fin)
open import Data.Fin.Subset using (Subset; ⊤; ⊥; _∈_; _∉_)
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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
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
open Gamma_one_Algebra isRoutingAlgebra n using (RoutingSet; RoutingVector; Øᵥ; _≈ᵥ_; ≈ᵥ-refl; ≈ᵥ-reflexive; ≈ᵥ-sym; ≈ᵥ-trans; _⊕ᵥ_; ⨁ₛ; ~_; ─_; _[_]; _〚_〛; FinRoute-setoid; FinRoute-decSetoid; 𝕍ₛ)
open Gamma_one_Properties isRoutingAlgebra A using (Γ₁-cong; ⊕-distributive; ⊕ᵥ-cong; Lemma-Γ₀=Γ₁; 〚〛-cong; []-cong; ⨁ₛ-cong; ⊕ₛ-cong; ≈ₘ⇒≈ᵥ)
open Gamma_two isRoutingAlgebra Imp Prot Exp using (Γ₂; Γ₂,ᵥ; Γ₂,ᵢ; Γ₂,ₒ)
open Gamma_two_Algebra isRoutingAlgebra n using (RoutingVector₂; RouteMapMatrix; toRouteMapMatrix; Øᵥ,₂; _≈ₐ,₂_; _〖_〗; _↓; _●_; _●ₘ_; _ᵀ)
open Gamma_two_Properties isRoutingAlgebra A Imp Prot Exp A=Imp∘Prot∘Exp using (Γ₁=Γ₂-comp; Γ₂-State-decSetoid; Γ₂-cong; Γ₂,ᵥ-cong; Γ₂,ᵢ-cong; Γ₂,ₒ-cong; ≈ᵥ,₂-decSetoid; LemmaA₃; f[]-cong)
open Omega_zero algebra A using (Ω₀; [_,_]_; [,]-⊤; [,]-⊥)
open Omega_one isRoutingAlgebra A using (Γ₁'; Ω₁'; Ω₁; _⟦_⟧'; Γ₁'-cong; Ω₁=Ω₀; Τ₁; r₁; Τ₁-cong)
open PermutationEq FinRoute-setoid
open PermutationProperties FinRoute-setoid using (_↭?_; ↭-decSetoid)
open DecSetoid FinRoute-decSetoid using () renaming (_≟_ to _≟ᵣ_; refl to ≈ᵣ-refl)
open DecSetoid Γ₂-State-decSetoid using () renaming (Carrier to Γ₂-State; _≈_  to _≈ₛ_ ; refl to ≈ₛ-refl; trans to ≈ₛ-trans; reflexive to ≈ₛ-reflexive; setoid to 𝕊ₛ)
open DecSetoid ≈ᵥ,₂-decSetoid using () renaming (_≈_ to _≈ᵥ,₂_; refl to ≈ᵥ,₂-refl; reflexive to ≈ᵥ,₂-reflexive; setoid to 𝕍₂ₛ)

-- TODO: Reorganise the lmv34 folder, split into Algebra/Properties files.
--       Clean-up the code files, includes organising imports conform standards.

--------------------------------------------------------------------------------
-- Algebra

-- Generalised export function application
infix 10 _【_】'
_【_】' : RouteMapMatrix → (Fin n → Fin n → RoutingSet) → RoutingVector₂
(F 【 f 】') i q = (F i q) [ f q i ]

-- Generalised (asynchronous) operator
Γ₂,ₒ' : (Fin n → Fin n → RoutingSet) → RoutingVector₂
Γ₂,ₒ' f = Exp 【 f 】'

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
-- Operation properties

infix 10 _||_||'
_||_||' : RouteMapMatrix → (Fin n → RoutingVector) → RoutingVector
(A || V ||' ) i = ⨁ₛ (λ q → (A i q) [ V i q ])

【】'-cong : ∀ {F V V'} → (∀ i → V i ≈ᵥ V' i) → F 【 V 】' ≈ᵥ,₂ F 【 V' 】'
【】'-cong V=V' i q = []-cong (V=V' q i)

Γ₂,ₒ'-cong : ∀ {V V'} → (∀ i → V i ≈ᵥ V' i) → Γ₂,ₒ' V ≈ᵥ,₂ Γ₂,ₒ' V'
Γ₂,ₒ'-cong = 【】'-cong

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

-- TODO: reorganise choice operator [,] properties to a separate file.
[_,_]-cong : ∀ {X X' Y Y' : RoutingVector} {S : Subset n} →
             X ≈ᵥ X' → Y ≈ᵥ Y' → [ X , Y ] S ≈ᵥ [ X' , Y' ] S
[_,_]-cong {X} {X'} {Y} {Y'} {S} X=X' Y=Y' i with i ∈? S
... | yes _ = X=X' i
... | no  _ = Y=Y' i

[,]-reasoning : ∀ {X Y W : RoutingVector} {S} →
                (∀ i → i ∈ S → X i ↭ W i) →
                (∀ i → i ∉ S → Y i ↭ W i) → 
                ([ X , Y ] S) ≈ᵥ W
[,]-reasoning {S = S} ∈S⇒↭ ∉S⇒↭ i with i ∈? S
... | no  i∉S = ∉S⇒↭ i i∉S
... | yes i∈S = ∈S⇒↭ i i∈S

[,]-reasoning₂ : ∀ {X Y W : RoutingVector₂} {S} →
                 (∀ i q → i ∈ S → X i q ↭ W i q) →
                 (∀ i q → i ∉ S → Y i q ↭ W i q) → 
                 ([ X , Y ] S) ≈ᵥ,₂ W
[,]-reasoning₂ {S = S} ∈S⇒↭ ∉S⇒↭ i q with i ∈? S
... | no  i∉S = ∉S⇒↭ i q i∉S
... | yes i∈S = ∈S⇒↭ i q i∈S


[,]-∉ : ∀ {X Y : RoutingVector} {S} i → i ∉ S → ([ X , Y ] S) i ↭ Y i
[,]-∉ {S = S} i i∉S with i ∈? S
... | no  _   = ↭-refl
... | yes i∈S = contradiction i∈S i∉S

[,]-∈ : ∀ {X Y : RoutingVector} {S} i → i ∈ S → ([ X , Y ] S) i ↭ X i
[,]-∈ {S = S} i i∈S with i ∈? S
... | no  i∉S = contradiction i∈S i∉S
... | yes _   = ↭-refl

--------------------------------------------------------------------------------
-- Implementation of Ω₂

-- A triple schedule, one for each component V, I, O
Schedule₃ : ℕ → Set
Schedule₃ n = (Schedule n) × (Schedule n) × (Schedule n)

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

ψ₃ˢʸⁿᶜ : Schedule₃ n
ψ₃ˢʸⁿᶜ = (ψˢʸⁿᶜ , ψˢʸⁿᶜ , ψˢʸⁿᶜ)

Ω₂'ˢʸⁿᶜ=Γ₂ : ∀ S {t} (accₜ : Acc _<_ t) → Ω₂' ψ₃ˢʸⁿᶜ S accₜ ≈ₛ (Γ₂ ^ t) S
Ω₂'ˢʸⁿᶜ=Γ₂ S {zero}  accₜ      = ≈ₛ-refl
Ω₂'ˢʸⁿᶜ=Γ₂ S {suc t} (acc rec) = begin
  Ω₂' ψ₃ˢʸⁿᶜ S (acc rec)                 ≡⟨⟩
  ([ Γ₂,ᵥ I[t] , V[t] ] αˢʸⁿᶜ (suc t)) ,
  ([ Γ₂,ᵢ O[t] , I[t] ] αˢʸⁿᶜ (suc t)) ,
  ([ Γ₂,ₒ V[t] , O[t] ] αˢʸⁿᶜ (suc t))   ≈⟨ ≈ᵥ-reflexive [,]-⊤ , ≈ᵥ,₂-reflexive [,]-⊤ , ≈ᵥ,₂-reflexive [,]-⊤ ⟩
  (Γ₂,ᵥ I[t]) , (Γ₂,ᵢ O[t]) , (Γ₂,ₒ V[t]) ≡⟨⟩
  Γ₂ (V[t] , I[t] , O[t])                ≈⟨ Γ₂-cong (Ω₂'ˢʸⁿᶜ=Γ₂ S (rec t ≤-refl)) ⟩
  (Γ₂ ^ (suc t)) S                       ∎
  where open EqReasoning 𝕊ₛ
        V[t] : RoutingVector
        V[t] = getV (Ω₂' ψ₃ˢʸⁿᶜ S (rec t ≤-refl))
        I[t] : RoutingVector₂
        I[t] = getI (Ω₂' ψ₃ˢʸⁿᶜ S (rec t ≤-refl))
        O[t] : RoutingVector₂
        O[t] = getO (Ω₂' ψ₃ˢʸⁿᶜ S (rec t ≤-refl))

Ω₂ˢʸⁿᶜ=Γ₂ : ∀ S t → Ω₂ ψ₃ˢʸⁿᶜ S t ≈ₛ (Γ₂ ^ t) S
Ω₂ˢʸⁿᶜ=Γ₂ S t = Ω₂'ˢʸⁿᶜ=Γ₂ S (<-wellFounded t)

--------------------------------------------------------------------------------
-- Reduction/transformation Ω₂ → Ω₁

-- Transformation Ω₂ → Ω₁
Τ₂ : Γ₂-State → RoutingVector
Τ₂ (V , I , O) = V

Τ₂-cong : ∀ {S S'} → S ≈ₛ S' → Τ₂ S ≈ᵥ Τ₂ S'
Τ₂-cong (V=V' , I=I' , O=O') = V=V'

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

  ϕ-inactive : ∀ t i j → i ∉ α (suc t) → ϕ (suc t) i j ≡ ϕ t i j
  ϕ-inactive t i j i∉α with i ∈? α (suc t)
  ... | no  _   = refl
  ... | yes i∈α = contradiction i∈α i∉α

  ϕ-active : ∀ t i j → i ∈ α (suc t) → ϕ (suc t) i j ≡ β (suc t) i j
  ϕ-active t i j i∈α with i ∈? α (suc t)
  ... | no  i∉α = contradiction i∈α i∉α
  ... | yes _   = refl

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
-- node i. It follows the cycle of data flow in Ω₂.

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
follow-cycle = tᵥ

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

--------------------------------------------------------------------------------
-- Proof of Ω₂ = Ω₁: the Ω₂ model is simulated by Ω₁.

S₀ : Γ₂-State
S₀ = (Øᵥ , Øᵥ,₂ , Øᵥ,₂)

module _ ((ψᵥ , ψᵢ , ψₒ) : Schedule₃ n)  where
  ψ : Schedule₃ n
  ψ = (ψᵥ , ψᵢ , ψₒ)
  
  open Schedule ψᵥ using () renaming (α to αᵥ; β to βᵥ; β-causality to βᵥ-causality)
  open Schedule ψᵢ using () renaming (α to αᵢ; β to βᵢ; β-causality to βᵢ-causality)
  open Schedule ψₒ using () renaming (α to αₒ; β to βₒ; β-causality to βₒ-causality)
  open Schedule (r₂ ψ) using () renaming (α to α'; β to β'; β-causality to β'-causality)

  -- Useful shortcuts for recursively calling accessible arguments.
  pred : ∀ {t} → Acc _<_ (suc t) → Acc _<_ t
  pred {t} (acc rec) = rec t ≤-refl

  acc[tᵢ] : ∀ {t} i → Acc _<_ (suc t) → Acc _<_ (tᵢ ψ (suc t) i)
  acc[tᵢ] {t} i (acc rec) = rec (tᵢ ψ (suc t) i) (s≤s (tᵢ≤t ψ t i))

  acc[tₒ] : ∀ {t} q i → Acc _<_ (suc t) → Acc _<_ (tₒ ψ (suc t) q i)
  acc[tₒ] {t} q i (acc rec) = rec (tₒ ψ (suc t) q i) (s≤s (tₒ≤t ψ t q i))

  acc[tᵥ] : ∀ {t} i q → Acc _<_ (suc t) → Acc _<_ (tᵥ ψ (suc t) i q)
  acc[tᵥ] {t} i q (acc rec) = rec (tᵥ ψ (suc t) i q) (s≤s (tᵥ≤t ψ t i q))

  acc[βᵥ] : ∀ {t} i → Acc _<_ (suc t) → Acc _<_ (βᵥ (suc t) i i)
  acc[βᵥ] {t} i (acc rec) = rec (βᵥ (suc t) i i) (s≤s (βᵥ-causality t i i))

  acc[βᵢ] : ∀ {t} i q → Acc _<_ (suc t) → Acc _<_ (βᵢ (suc t) i q)
  acc[βᵢ] {t} i q (acc rec) = rec (βᵢ (suc t) i q) (s≤s (βᵢ-causality t i q))

  acc[βₒ] : ∀ {t} q → Acc _<_ (suc t) → Acc _<_ (βₒ (suc t) q q)
  acc[βₒ] {t} q (acc rec) = rec (βₒ (suc t) q q) (s≤s (βₒ-causality t q q))

  acc[β'] : ∀ {t} i q → Acc _<_ (suc t) → Acc _<_ (β' (suc t) i q)
  acc[β'] {t} i q (acc rec) = rec (β' (suc t) i q) (s≤s (β'-causality t i q))

  acc[ϕ] : ∀ {t} i q (ψ : Schedule n) → Acc _<_ t → Acc _<_ (ϕ ψ t i q)
  acc[ϕ] {zero} i q ψ (acc rec) = acc rec
  acc[ϕ] {suc t} i q ψ (acc rec) = rec (ϕ ψ (suc t) i q) (s≤s (ϕ-causality ψ t i q))

  postulate
    Ω₂'-iter-cong : ∀ {t t'} {accₜ : Acc _<_ t} {accₜ' : Acc _<_ t'} →
                    t ≡ t' → Ω₂' ψ S₀ accₜ ≈ₛ Ω₂' ψ S₀ accₜ'

  V[t+1]-step : ∀ {t} (acc[t+1] : Acc _<_ (suc t)) →
                let V[t+1] = getV (Ω₂' ψ S₀ acc[t+1])
                    V[t] = getV (Ω₂' ψ S₀ (pred acc[t+1]))
                    I[tᵢ] = λ i q → getI (Ω₂' ψ S₀ (acc[tᵢ] i acc[t+1])) i q in
                V[t+1] ≈ᵥ [ Γ₂,ᵥ I[tᵢ] , V[t] ] αᵥ (suc t)
  V[t+1]-step {t} (acc rec) =
    [,]-reasoning {Γ₂,ᵥ I[βᵥ]} {V[t]} {[ Γ₂,ᵥ I[tᵢ] , V[t] ] αᵥ (suc t)} V[t+1]-active V[t+1]-inactive
    where V[t] : RoutingVector
          V[t] = getV (Ω₂' ψ S₀ (rec t ≤-refl))
          I[βᵥ] : RoutingVector₂
          I[βᵥ] i q = getI (Ω₂' ψ S₀ (acc[βᵥ] i (acc rec))) i q
          I[tᵢ] : RoutingVector₂
          I[tᵢ] i q = getI (Ω₂' ψ S₀ (acc[tᵢ] i (acc rec))) i q

          ∈⇒I[βᵥ]=I[tᵢ] : ∀ i q → i ∈ αᵥ (suc t) → I[βᵥ] i q ↭ I[tᵢ] i q
          ∈⇒I[βᵥ]=I[tᵢ] i q i∈α = getI=I' (Ω₂'-iter-cong (sym (ϕ-active ψᵥ t i i i∈α))) i q

          V[t+1]-active : ∀ i → i ∈ αᵥ (suc t) → Γ₂,ᵥ I[βᵥ] i ↭ ([ Γ₂,ᵥ I[tᵢ] , V[t] ] αᵥ (suc t)) i
          V[t+1]-active i i∈α = ↭-trans (⊕ₛ-cong (⨁ₛ-cong (λ {q} → ∈⇒I[βᵥ]=I[tᵢ] i q i∈α)) (≈ᵥ-refl {~ M} i))
                                        (↭-sym ([,]-∈ i i∈α))

          V[t+1]-inactive : ∀ i → i ∉ αᵥ (suc t) → V[t] i ↭ ([ Γ₂,ᵥ I[tᵢ] , V[t] ] αᵥ (suc t)) i
          V[t+1]-inactive i i∉α = ↭-sym ([,]-∉ i i∉α)
  
  I[t]-step : ∀ {t} (acc[t] : Acc _<_ t) →
                 let I[t] = getI (Ω₂' ψ S₀ acc[t])
                     O[ϕ[t]] = λ q i → getO (Ω₂' ψ S₀ (acc[ϕ] i q ψᵢ acc[t])) q i in
                 I[t] ≈ᵥ,₂ Γ₂,ᵢ O[ϕ[t]]
  I[t]-step {zero}  _         = ≈ᵥ,₂-refl
  I[t]-step {suc t} (acc rec) =
    [,]-reasoning₂ {Γ₂,ᵢ O[β[t+1]]} {I[t]} {Γ₂,ᵢ O[ϕ[t+1]]} ∈⇒I[t]=O[ϕ] ∉⇒I[t]=O[ϕ]
    where I[t+1] : RoutingVector₂
          I[t+1] = getI (Ω₂' ψ S₀ (acc rec))
          I[t] : RoutingVector₂
          I[t] = getI (Ω₂' ψ S₀ (rec t ≤-refl))
          O[β[t+1]] : RoutingVector₂
          O[β[t+1]] q i = getO (Ω₂' ψ S₀ (acc[βᵢ] i q (acc rec))) q i
          O[ϕ[t+1]] : RoutingVector₂
          O[ϕ[t+1]] q i = getO (Ω₂' ψ S₀ (acc[ϕ] i q ψᵢ (acc rec))) q i
          O[ϕ[t]] : RoutingVector₂
          O[ϕ[t]] q i = getO (Ω₂' ψ S₀ (acc[ϕ] i q ψᵢ (rec t ≤-refl))) q i

          O[ϕ[t+1]]=O[β[t+1]] : ∀ i q → i ∈ αᵢ (suc t) → O[β[t+1]] q i ↭ O[ϕ[t+1]] q i
          O[ϕ[t+1]]=O[β[t+1]] i q i∈α = ↭-sym (getO=O' (Ω₂'-iter-cong (ϕ-active ψᵢ t i q i∈α)) q i)

          ∈⇒I[t]=O[ϕ] : ∀ i q → i ∈ αᵢ (suc t) → (Γ₂,ᵢ O[β[t+1]]) i q ↭ (Γ₂,ᵢ O[ϕ[t+1]]) i q
          ∈⇒I[t]=O[ϕ] i q i∈αᵢ = []-cong (O[ϕ[t+1]]=O[β[t+1]] i q i∈αᵢ)
          
          O[ϕ[t+1]]=O[ϕ[t]] : ∀ i q → i ∉ αᵢ (suc t) → O[ϕ[t+1]] q i ↭ O[ϕ[t]] q i
          O[ϕ[t+1]]=O[ϕ[t]] i q i∉α = getO=O' (Ω₂'-iter-cong (ϕ-inactive ψᵢ t i q i∉α)) q i
          
          ∉⇒I[t]=O[ϕ] : ∀ i q → i ∉ αᵢ (suc t) → I[t] i q ↭ (Γ₂,ᵢ O[ϕ[t+1]]) i q
          ∉⇒I[t]=O[ϕ] i q i∉αᵢ = ↭-trans (I[t]-step {t} (rec t ≤-refl) i q) ([]-cong (↭-sym (O[ϕ[t+1]]=O[ϕ[t]] i q i∉αᵢ)))

  O[t]-step : ∀ {t} (acc[t] : Acc _<_ t) →
                 let O[t] = getO (Ω₂' ψ S₀ acc[t])
                     V[ϕ[t]] = λ q → getV (Ω₂' ψ S₀ (acc[ϕ] q q ψₒ acc[t])) q in
                 O[t] ≈ᵥ,₂ Γ₂,ₒ V[ϕ[t]]
  O[t]-step {zero}  _         = ≈ᵥ,₂-refl
  O[t]-step {suc t} (acc rec) = [,]-reasoning₂ {Γ₂,ₒ V[β[t+1]]} {O[t]} {Γ₂,ₒ V[ϕ[t+1]]} O[t+1]-active O[t+1]-inactive
    where O[t+1] : RoutingVector₂
          O[t+1] = getO (Ω₂' ψ S₀ (acc rec))
          O[t] : RoutingVector₂
          O[t] = getO (Ω₂' ψ S₀ (rec t ≤-refl))
          V[β[t+1]] : RoutingVector
          V[β[t+1]] q = getV (Ω₂' ψ S₀ (acc[βₒ] q (acc rec))) q 
          V[ϕ[t+1]] : RoutingVector
          V[ϕ[t+1]] q = getV (Ω₂' ψ S₀ (acc[ϕ] q q ψₒ (acc rec))) q
          V[ϕ[t]] : RoutingVector
          V[ϕ[t]] q = getV (Ω₂' ψ S₀ (acc[ϕ] q q ψₒ (rec t ≤-refl))) q

          ∈⇒V[β[t+1]]=V[ϕ[t+1]] : ∀ i → i ∈ αₒ (suc t) → V[β[t+1]] i ↭ V[ϕ[t+1]] i
          ∈⇒V[β[t+1]]=V[ϕ[t+1]] i i∈α = getV=V' (Ω₂'-iter-cong (sym (ϕ-active ψₒ t i i i∈α))) i

          O[t+1]-active : ∀ i q → i ∈ αₒ (suc t) → (Γ₂,ₒ V[β[t+1]]) i q ↭ (Γ₂,ₒ V[ϕ[t+1]]) i q
          O[t+1]-active i q i∈α = []-cong (∈⇒V[β[t+1]]=V[ϕ[t+1]] i i∈α)
          
          ∉⇒V[ϕ[t+1]]=V[ϕ[t]] : ∀ i → i ∉ αₒ (suc t) → V[ϕ[t+1]] i ↭ V[ϕ[t]] i
          ∉⇒V[ϕ[t+1]]=V[ϕ[t]] i i∉α = getV=V' (Ω₂'-iter-cong (ϕ-inactive ψₒ t i i i∉α)) i

          O[t+1]-inactive : ∀ i q → i ∉ αₒ (suc t) → O[t] i q ↭ (Γ₂,ₒ V[ϕ[t+1]]) i q 
          O[t+1]-inactive i q i∉α = ↭-trans (O[t]-step (rec t ≤-refl) i q) ([]-cong (↭-sym (∉⇒V[ϕ[t+1]]=V[ϕ[t]] i i∉α)))

  lem₂ : ∀ {t} (acc[t+1] : Acc _<_ (suc t)) →
         let I[tᵢ] = λ i q → getI (Ω₂' ψ S₀ (acc[tᵢ] i acc[t+1])) i q
             O[tₒ] = λ i q → getO (Ω₂' ψ S₀ (acc[tₒ] q i acc[t+1])) i q in
         I[tᵢ] ≈ᵥ,₂ Γ₂,ᵢ O[tₒ]
  lem₂ {t} (acc rec) = begin
    I[tᵢ]         ≈⟨ (λ i q → I[t]-step (acc[tᵢ] i (acc rec)) i q) ⟩
    Γ₂,ᵢ O[ϕ[tᵢ]] ≈⟨ (λ i q → Γ₂,ᵢ-cong (getO=O' (Ω₂'-iter-cong {t' = tₒ ψ (suc t) i q} refl)) i q) ⟩
    Γ₂,ᵢ O[tₒ]    ∎
    where open EqReasoning 𝕍₂ₛ
          I[tᵢ] : RoutingVector₂
          I[tᵢ] i q = getI (Ω₂' ψ S₀ (acc[tᵢ] i (acc rec))) i q
          O[tₒ] : RoutingVector₂
          O[tₒ] i q = getO (Ω₂' ψ S₀ (acc[tₒ] q i (acc rec))) i q
          O[ϕ[tᵢ]] : RoutingVector₂
          O[ϕ[tᵢ]] q i = getO (Ω₂' ψ S₀ (acc[ϕ] i q ψᵢ (acc[tᵢ] i (acc rec)))) q i

  lem₃ : ∀ {t} (acc[t+1] : Acc _<_ (suc t)) →
         let O[tₒ] = λ i q → getO (Ω₂' ψ S₀ (acc[tₒ] q i acc[t+1])) i q
             V[tᵥ] = λ i q → getV (Ω₂' ψ S₀ (acc[tᵥ] i q acc[t+1])) q in
         O[tₒ] ≈ᵥ,₂ Γ₂,ₒ' V[tᵥ]
  lem₃ {t} (acc rec) = begin
    O[tₒ]          ≈⟨ (λ i q → O[t]-step (acc[tₒ] q i (acc rec)) i q) ⟩
    Γ₂,ₒ' V[ϕ[tₒ]] ≈⟨ (λ i q → Γ₂,ₒ-cong (getV=V' (Ω₂'-iter-cong {t' = tᵥ ψ (suc t) q i} refl)) i q) ⟩
    Γ₂,ₒ' V[tᵥ]    ∎
    where open EqReasoning 𝕍₂ₛ
          O[tₒ] : RoutingVector₂
          O[tₒ] i q = getO (Ω₂' ψ S₀ (acc[tₒ] q i (acc rec))) i q
          V[ϕ[tₒ]] : RoutingVector₂
          V[ϕ[tₒ]] i q = getV (Ω₂' ψ S₀ (acc[ϕ] q q ψₒ (acc[tₒ] i q (acc rec)))) q
          V[tᵥ] : RoutingVector₂
          V[tᵥ] i q = getV (Ω₂' ψ S₀ (acc[tᵥ] i q (acc rec))) q          

  -- The crucial lemma. Relates one cycle of Ω₂ computations to one
  -- application of Ω₁.
  V[t+1]-cycle : ∀ {t} (acc[t+1] : Acc _<_ (suc t)) →
         let V[t+1]  = getV (Ω₂' ψ S₀ acc[t+1])
             V[t]    = getV (Ω₂' ψ S₀ (pred acc[t+1]))
             V[tᵥ] = λ i q → getV (Ω₂' ψ S₀ (acc[tᵥ] i q acc[t+1])) q in
         V[t+1] ≈ᵥ [ Γ₁' V[tᵥ] ,  V[t] ] αᵥ (suc t)
  V[t+1]-cycle {t} acc[t+1] = begin
    V[t+1]                                         ≈⟨ V[t+1]-step acc[t+1] ⟩
    [ Γ₂,ᵥ I[tᵢ] , V[t] ] αᵥ (suc t)                ≈⟨ [_,_]-cong (Γ₂,ᵥ-cong (lem₂ acc[t+1])) ≈ᵥ-refl ⟩
    [ Γ₂,ᵥ (Γ₂,ᵢ O[tₒ]) , V[t] ] αᵥ (suc t)         ≈⟨ [_,_]-cong (Γ₂,ᵥ-cong (Γ₂,ᵢ-cong (lem₃ acc[t+1]))) ≈ᵥ-refl ⟩
    [ Γ₂,ᵥ (Γ₂,ᵢ (Γ₂,ₒ' V[tᵥ])) , V[t] ] αᵥ (suc t) ≈⟨ [_,_]-cong (≈ᵥ-sym (Γ₁=Γ₂-comp' V[tᵥ])) ≈ᵥ-refl ⟩
    [ Γ₁' V[tᵥ] , V[t] ] αᵥ (suc t)       ∎
    where open EqReasoning 𝕍ₛ
          V[t+1] : RoutingVector
          V[t+1] = getV (Ω₂' ψ S₀ acc[t+1])
          V[t] : RoutingVector
          V[t] = getV (Ω₂' ψ S₀ (pred acc[t+1]))
          I[tᵢ] : RoutingVector₂
          I[tᵢ] i q = getI (Ω₂' ψ S₀ (acc[tᵢ] i acc[t+1])) i q
          O[tₒ] : RoutingVector₂
          O[tₒ] i q = getO (Ω₂' ψ S₀ (acc[tₒ] q i acc[t+1])) i q
          V[tᵥ] : Fin n → RoutingVector
          V[tᵥ] i q = getV (Ω₂' ψ S₀ (acc[tᵥ] i q acc[t+1])) q

  Ω₂'=Ω₁' : ∀ {t} (acc[t] : Acc _<_ t) → Τ₂ (Ω₂' ψ S₀ acc[t]) ≈ᵥ Ω₁' (r₂ ψ) (Τ₂ S₀) acc[t]
  Ω₂'=Ω₁' {zero} _    = ≈ᵥ-refl
  Ω₂'=Ω₁' {suc t} (acc rec) = begin
    Τ₂ (Ω₂' ψ S₀ (acc rec))           ≡⟨⟩
    V₂[t+1]                          ≈⟨ V[t+1]-cycle (acc rec) ⟩
    [ Γ₁' V₂[tᵥ] , V₂[t] ] αᵥ (suc t) ≈⟨ [_,_]-cong (Γ₁'-cong V₂[tᵥ]=V₁[tᵥ]) V₂[t]=V₁[t] ⟩
    [ Γ₁' V₁[tᵥ] , V₁[t] ] αᵥ (suc t) ≡⟨⟩
    Ω₁' (r₂ ψ) (Τ₂ S₀) (acc rec)      ∎
      where open EqReasoning 𝕍ₛ
            V₂[t+1] : RoutingVector
            V₂[t+1] = getV (Ω₂' ψ S₀ (acc rec))
            V₂[t] : RoutingVector
            V₂[t] = getV (Ω₂' ψ S₀ (pred (acc rec)))
            V₂[tᵥ] : Fin n → RoutingVector
            V₂[tᵥ] i q = getV (Ω₂' ψ S₀ (acc[tᵥ] i q (acc rec))) q
            V₁[t+1] : RoutingVector
            V₁[t+1] = Ω₁' (r₂ ψ) (Τ₂ S₀) (acc rec)
            V₁[t] : RoutingVector
            V₁[t] = Ω₁' (r₂ ψ) (Τ₂ S₀) (pred (acc rec))
            V₁[tᵥ] : Fin n → RoutingVector
            V₁[tᵥ] i q = Ω₁' (r₂ ψ) (Τ₂ S₀) (acc[tᵥ] i q (acc rec)) q

            V₂[tᵥ]=V₁[tᵥ] : V₂[tᵥ] ≈ᵥ,₂ V₁[tᵥ]
            V₂[tᵥ]=V₁[tᵥ] i q = Ω₂'=Ω₁' (rec (tᵥ ψ (suc t) i q) (s≤s (tᵥ≤t ψ t i q))) q

            V₂[t]=V₁[t] : V₂[t] ≈ᵥ V₁[t]
            V₂[t]=V₁[t] = Ω₂'=Ω₁' (rec t ≤-refl)

Ω₂=Ω₁ : ∀ ψ t → Τ₂ (Ω₂ ψ S₀ t) ≈ᵥ Ω₁ (r₂ ψ) (Τ₂ S₀) t
Ω₂=Ω₁ ψ t = Ω₂'=Ω₁' ψ (<-wellFounded t)

Ω₂=Ω₀ : ∀ ψ t → (Τ₁ ∘ Τ₂) (Ω₂ ψ S₀ t) ≈ₘ Ω₀ ((r₁ ∘ r₂) ψ) ((Τ₁ ∘ Τ₂) S₀) t
Ω₂=Ω₀ ψ t = begin
  (Τ₁ ∘ Τ₂) (Ω₂ ψ S₀ t)             ≈⟨ Τ₁-cong (Ω₂=Ω₁ ψ t) ⟩
  Τ₁ (Ω₁ (r₂ ψ) (Τ₂ S₀) t)          ≈⟨ Ω₁=Ω₀ (r₂ ψ) (Τ₂ S₀) t ⟩
  Ω₀ ((r₁ ∘ r₂) ψ) ((Τ₁ ∘ Τ₂) S₀) t ∎
    where open EqReasoning ℝ𝕄ₛ
