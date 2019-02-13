--------------------------------------------------------------------------------
-- This module contains a proof that if F obeys the synchronous conditions then
-- F is an ACO and hence that δ converges. It should be noted that the
-- synchronous conditions are modified from those proposed by Uresin and Dubois
-- in Proposition 3 in that they require the synchronous fixed point to be
-- unique. The file:
--
--   RoutingLib.Iteration.Asynchronous.Static.Convergence.UresinDubois3-Counterexample
--
-- contains a counter-example to Uresin & Dubois' original formulation.
--------------------------------------------------------------------------------

open import RoutingLib.Iteration.Asynchronous.Static
open import RoutingLib.Iteration.Asynchronous.Static.Convergence.Conditions

module RoutingLib.Iteration.Asynchronous.Static.Convergence.SynchronousImpliesACO
  {a ℓ n p o} (I∥ : AsyncIterable a ℓ n)
  (sync : SynchronousConditions I∥ p o)
  where

open import Data.Fin using (Fin)
open import Data.Product using (_×_; ∃; proj₁; proj₂; _,_; ∃₂)
open import Data.Nat as ℕ
  using (ℕ; zero; suc; _≤_; _+_; z≤n; s≤s; _≤?_; _∸_)
open import Data.Nat.Properties as ℕₚ
  using (pred-mono; ≰⇒≥; +-suc; +-comm; +-identityʳ; ≤-step)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (_∈_)

open import RoutingLib.Data.Table using (Table)
open import RoutingLib.Data.Nat.Properties using (m≤n⇒o+m≡n)
open import RoutingLib.Relation.Binary.Indexed.Homogeneous
open import RoutingLib.Relation.Unary.Indexed

open import RoutingLib.Iteration.Synchronous using (_^_)

open AsyncIterable I∥
open SynchronousConditions sync

σ : ℕ → S → S
σ k = (F ^ k)

--------------------------------------------------------------------------------
-- Proof
  
module _ {x} (x∈B : x ∈ᵢ B) where

  σᵏ*x≈x* : σ k* x ≈ x*
  σᵏ*x≈x* = σ-convergesTo-x* x∈B

  -- Proofs

  σᵏx∈B : ∀ k → σ k x ∈ᵢ B
  σᵏx∈B zero    = x∈B
  σᵏx∈B (suc K) = B-closed (σᵏx∈B K)
  
  σ-mono : ∀ {k t} → k ≤ t → σ t x ≤ₛ σ k x
  σ-mono {zero}  {zero}  z≤n       = ≤-refl
  σ-mono {zero}  {suc k} z≤n       = ≤-trans (F-decreasing (σᵏx∈B k)) (σ-mono {0} {k} z≤n)
  σ-mono {suc k} {suc t} (s≤s k≤t) = F-monotone (σᵏx∈B t) (σᵏx∈B k) (σ-mono k≤t)

  σ-fixed′ : ∀ t → σ (t + k*) x ≈ x*
  σ-fixed′ zero    = σᵏ*x≈x*
  σ-fixed′ (suc t) = ≈-trans (F-cong (σ-fixed′ t)) x*-fixed

  σ-fixed : ∀ {t} → k* ≤ t → σ t x ≈ x*
  σ-fixed T≤t with m≤n⇒o+m≡n T≤t
  ... | s , refl = σ-fixed′ s
  
  x*≤σᵏx : ∀ k → x* ≤ₛ σ k x
  x*≤σᵏx t with t ≤? k*
  ... | yes t≤T = ≤-respˡ-≈ (σᵏ*x≈x*) (σ-mono t≤T)
  ... | no  t≰T = ≤-reflexive (≈-sym (σ-fixed (≰⇒≥ t≰T)))

  x*≤x∈B : x* ≤ₛ x
  x*≤x∈B = x*≤σᵏx 0
  
x*∈B : x* ∈ᵢ B
x*∈B = B-cong (σᵏ*x≈x* xₚ∈B) (σᵏx∈B xₚ∈B k*)




-- Sequence of sets

D : ℕ → IPred Sᵢ _
D k i xᵢ = (xᵢ ∈ B i) × (x* i ≤ᵢ xᵢ) × (∃ λ y → y ∈ᵢ B × xᵢ ≤ᵢ σ k y i)

Dᵢ-cong : ∀ {k i} {x y : Sᵢ i} → x ≈ᵢ y → x ∈ D k i → y ∈ D k i
Dᵢ-cong x≈y (x∈Bᵢ , x*ᵢ≤x , y , y∈B , x≤σᵏyᵢ) =
  Bᵢ-cong x≈y x∈Bᵢ ,
  ≤ᵢ-respʳ-≈ᵢ x≈y x*ᵢ≤x ,
  (y , y∈B , ≤ᵢ-respˡ-≈ᵢ x≈y x≤σᵏyᵢ)

F-resp-D₀ : ∀ {x} → x ∈ᵢ D 0 → F x ∈ᵢ D 0
F-resp-D₀ x∈D₀ i =
  B-closed x∈D i ,
  x*≤σᵏx x∈D 1 i ,
  y , y∈B , ≤ᵢ-trans (F-decreasing x∈D i) xᵢ≤σᵏyᵢ
  where
  x∈D    = proj₁ ∘ x∈D₀
  y      = (proj₁ ∘ proj₂ ∘ proj₂ ∘ x∈D₀) i
  y∈B    = (proj₁ ∘ proj₂ ∘ proj₂ ∘ proj₂ ∘ x∈D₀) i
  xᵢ≤σᵏyᵢ = (proj₂ ∘ proj₂ ∘ proj₂ ∘ proj₂ ∘ x∈D₀) i
  
  
D-finish₁ : ∀ k → x* ∈ᵢ D k
D-finish₁ k i = x*∈B i , ≤ᵢ-refl , x* , x*∈B , ≤ᵢ-reflexive {!!}

D-finish₂ : ∀ {k} → k* ≤ k → ∀ {x} → x ∈ᵢ D k → x ≈ x*
D-finish₂ k*≤k x∈Dₖ i with x∈Dₖ i
... | (xᵢ∈Bᵢ , x*ᵢ≤xᵢ , y , y∈B , xᵢ≤σᵏxᵢ) =
  ≤ᵢ-antisym (≤ᵢ-trans xᵢ≤σᵏxᵢ (≤ᵢ-reflexive (σ-fixed y∈B k*≤k i) )) x*ᵢ≤xᵢ
  where
  x*≤x = proj₁ ∘ proj₂ ∘ x∈Dₖ
  x≤σᵏ = proj₂ ∘ proj₂ ∘ x∈Dₖ

D-finish : ∀ {k} → k* ≤ k → Singletonᵢ _≈_ (D k) x*
D-finish {k} k*≤k = D-finish₁ k , D-finish₂ k*≤k

F-mono-D  : ∀ {k x} → x ∈ᵢ D k → F x ∈ᵢ D (suc k)
F-mono-D {k} {x} x∈Dₖ i =
  B-closed x∈B i ,
  ≤-respˡ-≈ x*-fixed (F-monotone x*∈B x∈B x*≤x) i ,
  x , x∈B , {!!}
  where
  x∈B = proj₁ ∘ x∈Dₖ
  x*≤x = proj₁ ∘ proj₂ ∘ x∈Dₖ
  y      = λ i → (proj₁ ∘ proj₂ ∘ proj₂ ∘ x∈Dₖ) i i
  y∈B    = λ i → (proj₁ ∘ proj₂ ∘ proj₂ ∘ proj₂ ∘ x∈Dₖ) i i

  x≤σᵏy : x ≤ₛ σ k y
  x≤σᵏy j = {!!} --λ i → (proj₂ ∘ proj₂ ∘ proj₂ ∘ proj₂ ∘ x∈Dₖ) i

D₀⊆B : ∀ {x} → x ∈ᵢ D 0 → x ∈ᵢ B
D₀⊆B x∈D = proj₁ ∘ x∈D

B⊆D₀ : ∀ {x} → x ∈ᵢ B → x ∈ᵢ D 0
B⊆D₀ {x} x∈B i = x∈B i , x*≤x∈B x∈B i , x , x∈B , ≤ᵢ-refl

aco : ACO I∥ _
aco = record
  { B         = D
  ; Bᵢ-cong    = λ {k} → Dᵢ-cong {k}
  ; F-resp-B₀ = F-resp-D₀
  ; F-mono-B  = λ {k} → F-mono-D {k}
  ; x*        = x*
  ; k*        = k*
  ; B-finish  = D-finish
  }
