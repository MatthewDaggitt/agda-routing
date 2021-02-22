--------------------------------------------------------------------------------
-- Agda routing library
--
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

open import RoutingLib.Relation.Unary.Indexed

open import RoutingLib.Iteration.Asynchronous.Static
open import RoutingLib.Iteration.Asynchronous.Static.Convergence.Conditions

module RoutingLib.Iteration.Asynchronous.Static.Convergence.SyncImpliesACO
  {a ℓ n p o} (I∥ : AsyncIterable a ℓ n)
  {X₀ : IPred _ p} (sync : PartialSynchronousConditions I∥ X₀ o)
  where

open import Data.Fin using (Fin)
open import Data.Product using (_×_; ∃; proj₁; proj₂; _,_; ∃₂)
open import Data.Nat as ℕ
  using (ℕ; zero; suc; _≤_; _+_; z≤n; s≤s; _≤?_; _∸_)
open import Data.Nat.Properties as ℕₚ
  using (pred-mono; ≰⇒≥; +-suc; +-comm; +-identityʳ; ≤-step)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
import Relation.Binary.Reasoning.Setoid as EqReasoning
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (_∈_)

open import RoutingLib.Data.Nat.Properties using (m≤n⇒o+m≡n)
open import RoutingLib.Relation.Binary.Indexed.Homogeneous

open import RoutingLib.Iteration.Synchronous using (_^_)

open AsyncIterable I∥
open PartialSynchronousConditions sync

σ : ℕ → S → S
σ k = (F ^ k)

--------------------------------------------------------------------------------
-- Proof
  
module _ {x} (x∈X₀ : x ∈ᵢ X₀) where

  σᵏ*x≈x* : σ k* x ≈ x*
  σᵏ*x≈x* = σ-convergesTo-x* x∈X₀

  -- Proofs

  σᵏx∈X₀ : ∀ k → σ k x ∈ᵢ X₀
  σᵏx∈X₀ zero    = x∈X₀
  σᵏx∈X₀ (suc K) = X₀-closed (σᵏx∈X₀ K)
  
  σ-mono : ∀ {k t} → k ≤ t → σ t x ≤ₛ σ k x
  σ-mono {zero}  {zero}  z≤n       = ≤-refl
  σ-mono {zero}  {suc k} z≤n       = ≤-trans (F-decreasing (σᵏx∈X₀ k)) (σ-mono {0} {k} z≤n)
  σ-mono {suc k} {suc t} (s≤s k≤t) = F-monotone (σᵏx∈X₀ t) (σᵏx∈X₀ k) (σ-mono k≤t)

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

  x*≤x∈X₀ : x* ≤ₛ x
  x*≤x∈X₀ = x*≤σᵏx 0

  σᵏx*≈x* : ∀ k → σ k x* ≈ x*
  σᵏx*≈x* zero    = ≈-refl
  σᵏx*≈x* (suc k) = ≈-trans (F-cong (σᵏx*≈x* k)) x*-fixed


  x*∈B : x* ∈ᵢ X₀
  x*∈B = X₀-cong σᵏ*x≈x* (σᵏx∈X₀ k*)




-- Sequence of sets

module _ {y} (y∈X₀ : y ∈ᵢ X₀) where

  B : ℕ → IPred Sᵢ _
  B k i xᵢ = (xᵢ ∈ X₀ i) × (x* i ≤ᵢ xᵢ) × (xᵢ ≤ᵢ σ k y i)

  Bᵢ-cong : ∀ {k i} {x y : Sᵢ i} → x ≈ᵢ y → x ∈ B k i → y ∈ B k i
  Bᵢ-cong x≈y (x∈Bᵢ , x*ᵢ≤x , x≤σᵏyᵢ) =
    X₀ᵢ-cong x≈y x∈Bᵢ ,
    ≤ᵢ-respʳ-≈ᵢ x≈y x*ᵢ≤x ,
    ≤ᵢ-respˡ-≈ᵢ x≈y x≤σᵏyᵢ

  F-resp-B₀ : ∀ {x} → x ∈ᵢ B 0 → F x ∈ᵢ B 0
  F-resp-B₀ x∈B₀ i =
    X₀-closed x∈B i ,
    x*≤σᵏx x∈B 1 i ,
    ≤ᵢ-trans (F-decreasing x∈B i) ((proj₂ ∘ proj₂ ∘ x∈B₀) i)
    where x∈B = proj₁ ∘ x∈B₀

  B-finish₁ : ∀ k → x* ∈ᵢ B k
  B-finish₁ k i = x*∈B y∈X₀ i , ≤ᵢ-refl , x*≤σᵏx y∈X₀ k i

  B-finish₂ : ∀ {k} → k* ≤ k → ∀ {x} → x ∈ᵢ B k → x ≈ x*
  B-finish₂ k*≤k x∈Bₖ i with x∈Bₖ i
  ... | (_ , x*ᵢ≤xᵢ , xᵢ≤σᵏxᵢ) =
    ≤ᵢ-antisym (≤ᵢ-trans xᵢ≤σᵏxᵢ (≤ᵢ-reflexive (σ-fixed y∈X₀ k*≤k i) )) x*ᵢ≤xᵢ

  B-finish : ∀ {k} → k* ≤ k → Singletonᵢ _≈_ (B k) x*
  B-finish {k} k*≤k = B-finish₁ k , B-finish₂ k*≤k

  F-mono-B  : ∀ {k x} → x ∈ᵢ B k → F x ∈ᵢ B (suc k)
  F-mono-B {k} {x} x∈Bₖ i =
    X₀-closed x∈B i ,
    x*≤σᵏx x∈B 1 i ,
    F-monotone x∈B (σᵏx∈X₀ y∈X₀ k) (proj₂ ∘ proj₂ ∘ x∈Bₖ) i
    where x∈B = proj₁ ∘ x∈Bₖ

  y∈B₀ : y ∈ᵢ B 0
  y∈B₀ i = y∈X₀ i , x*≤x∈X₀ y∈X₀ i , ≤ᵢ-refl

  aco : PartialACO I∥ (B 0) _
  aco = record
    { B         = B
    ; X₀≋B₀     = id , id
    ; Bᵢ-cong   = λ {k} → Bᵢ-cong {k}
    ; F-resp-X₀ = F-resp-B₀
    ; F-mono-B  = λ {k} → F-mono-B {k}
    ; x*        = x*
    ; k*        = k*
    ; B-finish  = B-finish
    }
