open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
open import RoutingLib.Routing as Routing using () renaming (AdjacencyMatrix to AdjacencyMatrix')

module RoutingLib.lmv34.Asynchronous.Omega_one.Properties
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  {n} (A : AdjacencyMatrix' algebra n)
  where

open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.List using (tabulate)
open import Data.Nat using (zero; suc; _<_; s≤s)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Function.Base using (_∘_)
open import Induction.WellFounded using (Acc; acc)
import Relation.Binary.Reasoning.Setoid as EqReasoning
open import Relation.Nullary using (yes; no)

open import RoutingLib.Iteration.Synchronous using (_^_)
open import RoutingLib.Iteration.Asynchronous.Static.Schedule.Construct.Synchronous using (ψˢʸⁿᶜ; αˢʸⁿᶜ)
open import RoutingLib.Iteration.Asynchronous.Static.Schedule using (Schedule)
open import RoutingLib.lmv34.Asynchronous.Omega_zero algebra A
open import RoutingLib.lmv34.Asynchronous.Omega_zero.Algebra algebra A using ([_,_]_; _❪_❫; Γ₀')
open import RoutingLib.lmv34.Asynchronous.Omega_zero.Properties algebra A using (Γ₀'-cong; [,]-⊤ᵢ)
open import RoutingLib.lmv34.Asynchronous.Omega_one isRoutingAlgebra A
open import RoutingLib.lmv34.Asynchronous.Omega_one.Algebra isRoutingAlgebra A
open import RoutingLib.lmv34.Synchronous.Gamma_zero.Algebra algebra n using (_⊕ₘ_; ⨁)
open import RoutingLib.lmv34.Synchronous.Gamma_zero.Properties algebra A using (⊕ₘ-cong)
open import RoutingLib.lmv34.Synchronous.Gamma_one isRoutingAlgebra A using (Γ₁)
open import RoutingLib.lmv34.Synchronous.Gamma_one.Algebra isRoutingAlgebra n
open import RoutingLib.lmv34.Synchronous.Gamma_one.Properties isRoutingAlgebra A

open RawRoutingAlgebra algebra using (≈-refl; _▷_)
open Routing algebra n using (RoutingMatrix; I; ℝ𝕄ₛ; ≈ₘ-refl) renaming (_≈ₘ_ to infix 4 _≈ₘ_)

--------------------------------------------------------------------------------
-- Operation properties

-- TODO: Try to merely have a unique destination postulate for
-- RoutingVectors.
postulate
  ~-─-inverse : ∀ V → ~(─ V) ≈ᵥ V -- requires uniqueness of destination
  ─-~-inverse : ∀ X → ─(~ X) ≈ₘ X
  ─-cong : ∀ {U V} → U ≈ᵥ V → ─ U ≈ₘ ─ V -- requires uniqueness of destination

⟦_⟧-cong' : ∀ {A} {V V'} → (∀ i → V i ≈ᵥ V' i) → A ⟦ V ⟧' ≈ᵥ A ⟦ V' ⟧'
⟦_⟧-cong' V=V' i = ⨁ₛ-cong (λ {q} → []-cong (V=V' i q))

Γ₁'-cong : ∀ {V V'} → (∀ i → V i ≈ᵥ V' i) → Γ₁' V ≈ᵥ Γ₁' V'
Γ₁'-cong V=V' = ⊕ᵥ-cong (⟦_⟧-cong' V=V') (≈ᵥ-refl {~ I})

Τ₁-cong : ∀ {V V'} → V ≈ᵥ V' → Τ₁ V ≈ₘ Τ₁ V'
Τ₁-cong = ─-cong

─-⊕-distributive : ∀ U V → ─ (U ⊕ᵥ V) ≈ₘ (─ U) ⊕ₘ (─ V)
─-⊕-distributive U V = begin
  ─ (U ⊕ᵥ V)               ≈⟨ ─-cong (⊕ᵥ-cong (≈ᵥ-sym (~-─-inverse U)) (≈ᵥ-sym (~-─-inverse V))) ⟩
  ─ ((~(─ U)) ⊕ᵥ (~(─ V))) ≈⟨ ─-cong (≈ᵥ-sym (⊕ᵥ-distributive (─ U) (─ V))) ⟩
  ─ (~ ((─ U) ⊕ₘ (─ V)))   ≈⟨ ─-~-inverse ((─ U) ⊕ₘ (─ V)) ⟩
  (─ U) ⊕ₘ (─ V)           ∎
  where open EqReasoning ℝ𝕄ₛ

Lemma-Γ₀'=Γ₁' : ∀ {A Y} → A ⟦ ~' Y ⟧' ≈ᵥ ~ (A ❪ Y ❫)
Lemma-Γ₀'=Γ₁' {A} {Y} i = begin
  (A ⟦ ~' Y ⟧') i                                           ≡⟨⟩
  ⨁ₛ (λ q → (A i q ▷_) [ (~' Y) i q ])                     ≡⟨⟩
  ⨁ₛ (λ q → (λ s → (A i q) ▷ s) [ (~' Y) i q ])            ≡⟨⟩  
  ⨁ₛ (λ q → (map₂ (λ v → (A i q) ▷ v) ((~' Y) i q)) †)     ↭⟨ ⨁ₛ-cong (λ {q} → ~-lemma {i} {q} {Y i} {A}) ⟩
  ⨁ₛ (λ q → (tabulate λ d → (d , (A i q) ▷ (Y i q d))) †)  ↭⟨ LemmaA₂-iter (λ q d → (A i q) ▷ (Y i q d)) ⟩
  (tabulate λ q → (q , ⨁ (λ k → (A i k) ▷ (Y i k q)))) †   ≡⟨⟩
  (tabulate λ q → (q , (A ❪ Y ❫) i q)) †                   ≡⟨⟩
  (~ (A ❪ Y ❫)) i                                          ∎
  where open PermutationReasoning

─-⟦_⟧'-distributive : ∀ A V → ─ (A ⟦ V ⟧') ≈ₘ A ❪ ─' V ❫
─-⟦_⟧'-distributive A V = begin
  ─ (A ⟦ V ⟧')         ≈⟨ ─-cong (⟦_⟧-cong' (λ i → ≈ᵥ-sym (~-─-inverse (V i)))) ⟩
  ─ (A ⟦ ~'(─' V) ⟧')  ≈⟨ ─-cong Lemma-Γ₀'=Γ₁' ⟩
  ─ (~ (A ❪ ─' V ❫))  ≈⟨ ─-~-inverse (A ❪ ─' V ❫) ⟩
  A ❪ ─' V ❫          ∎
  where open EqReasoning ℝ𝕄ₛ
  
-- Theorem 3 (dual)
Γ₀'=Γ₁'-dual : ∀ V → ─(Γ₁' V) ≈ₘ Γ₀' (─' V)
Γ₀'=Γ₁'-dual V = begin
  ─(Γ₁' V)             ≡⟨⟩
  ─(A ⟦ V ⟧' ⊕ᵥ ~ I)    ≈⟨ ─-⊕-distributive (A ⟦ V ⟧') (~ I) ⟩
  ─(A ⟦ V ⟧') ⊕ₘ ─(~ I) ≈⟨ ⊕ₘ-cong (─-⟦_⟧'-distributive A V) (─-~-inverse I) ⟩
  A ❪ ─' V ❫ ⊕ₘ I      ≡⟨⟩
  Γ₀' (─' V) ∎
  where open EqReasoning ℝ𝕄ₛ

[_,_]-cong : ∀ {X X' Y Y' : RoutingMatrix} {S : Subset n} →
             X ≈ₘ X' → Y ≈ₘ Y' → [ X , Y ] S ≈ₘ [ X' , Y' ] S
[_,_]-cong {X} {X'} {Y} {Y'} {S} X=X' Y=Y' i with i ∈? S
... | yes _ = X=X' i
... | no  _ = Y=Y' i

─-[_,_]-distributive : ∀ U V S → ─([ U , V ] S) ≈ₘ [ (─ U) , (─ V) ] S
─-[_,_]-distributive U V S i j with i ∈? S
... | yes _ = ≈-refl
... | no _  = ≈-refl

--------------------------------------------------------------------------------
-- Proof that synchronous Ω₁ is indeed Γ₁

Ω₁'ˢʸⁿᶜ=Γ₁ : ∀ V {t} (acc[t] : Acc _<_ t) → Ω₁' ψˢʸⁿᶜ V acc[t] ≈ᵥ (Γ₁ ^ t) V
Ω₁'ˢʸⁿᶜ=Γ₁ V {zero}  _         = ≈ᵥ-refl
Ω₁'ˢʸⁿᶜ=Γ₁ V {suc t} (acc rec) = begin
  Ω₁' ψˢʸⁿᶜ V (acc rec)            ≡⟨⟩
  [ Γ₁ V[t] , V[t] ] αˢʸⁿᶜ (suc t) ≈⟨ ↭-reflexive ∘ [,]-⊤ᵢ ⟩
  Γ₁ V[t]                          ≈⟨ Γ₁-cong (Ω₁'ˢʸⁿᶜ=Γ₁ V (rec t ≤-refl)) ⟩
  (Γ₁ ^ (suc t)) V                 ∎
  where open EqReasoning 𝕍ₛ
        V[t] : RoutingVector
        V[t] = Ω₁' ψˢʸⁿᶜ V (rec t ≤-refl)

Ω₁ˢʸⁿᶜ=Γ₁ : ∀ V t → Ω₁ ψˢʸⁿᶜ V t ≈ᵥ (Γ₁ ^ t) V
Ω₁ˢʸⁿᶜ=Γ₁ V t = Ω₁'ˢʸⁿᶜ=Γ₁ V (<-wellFounded t)

--------------------------------------------------------------------------------
-- Proof of Ω₁ = Ω₀: the Ω₁ model is simulated by Ω₀.

module _ (ψ : Schedule n) where
  open Schedule ψ
  Ω₁'=Ω₀' : ∀ V {t} (acc[t] : Acc _<_ t) → Τ₁ (Ω₁' ψ V acc[t]) ≈ₘ Ω₀' (r₁ ψ) (Τ₁ V) acc[t]
  Ω₁'=Ω₀' V {zero}  _         = ≈ₘ-refl
  Ω₁'=Ω₀' V {suc t} (acc rec) = begin
    Τ₁ (Ω₁' ψ V (acc rec))                    ≡⟨⟩
    ─ (Ω₁' ψ V (acc rec))                     ≡⟨⟩
    ─ ([ Γ₁' V[β[t+1]] , V[t] ] α (suc t))    ≈⟨ ─-[_,_]-distributive (Γ₁' V[β[t+1]]) V[t] (α (suc t)) ⟩
    [ ─ (Γ₁' V[β[t+1]])  , ─ V[t] ] α (suc t) ≈⟨ [_,_]-cong (Γ₀'=Γ₁'-dual V[β[t+1]]) ─V[t]=X[t] ⟩
    [ Γ₀' (─' V[β[t+1]]) , X[t]   ] α (suc t) ≈⟨ [_,_]-cong (Γ₀'-cong ─V[β[t+1]]=X[β[t+1]]) ≈ₘ-refl ⟩
    [ Γ₀' (X[β[t+1]])    , X[t]   ] α (suc t) ≈⟨ ≈ₘ-refl ⟩
    Ω₀' (r₁ ψ) (Τ₁ V) (acc rec)               ∎
    where open EqReasoning ℝ𝕄ₛ
          V[t] : RoutingVector
          V[t] = Ω₁' ψ V (rec t ≤-refl)
          V[β[t+1]] : Fin n → RoutingVector
          V[β[t+1]] i q = Ω₁' ψ V (rec (β (suc t) i q) (s≤s (β-causality t i q))) q
          X[β[t+1]] : Fin n → RoutingMatrix
          X[β[t+1]] i q j = Ω₀' (r₁ ψ) (Τ₁ V) (rec (β (suc t) i q) (s≤s (β-causality t i q))) q j
          X[t] : RoutingMatrix
          X[t] = Ω₀' (r₁ ψ) (Τ₁ V) (rec t ≤-refl)

          ─V[β[t+1]]=X[β[t+1]] : ∀ i → (─' V[β[t+1]]) i ≈ₘ X[β[t+1]] i
          ─V[β[t+1]]=X[β[t+1]] i q j = Ω₁'=Ω₀' V (rec (β (suc t) i q) (s≤s (β-causality t i q))) q j

          ─V[t]=X[t] : ─ V[t] ≈ₘ X[t]
          ─V[t]=X[t] = Ω₁'=Ω₀' V (rec t ≤-refl)

Ω₁=Ω₀ : ∀ ψ V t → Τ₁ (Ω₁ ψ V t) ≈ₘ Ω₀ (r₁ ψ) (Τ₁ V) t
Ω₁=Ω₀ ψ V t = Ω₁'=Ω₀' ψ V (<-wellFounded t)
