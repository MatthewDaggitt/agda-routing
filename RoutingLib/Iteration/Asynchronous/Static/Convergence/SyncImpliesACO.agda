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
  {B₀ : IPred _ p} (sync : PartialSynchronousConditions I∥ B₀ o)
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
  
module _ {x} (x∈B₀ : x ∈ᵢ B₀) where

  σᵏ*x≈x* : σ k* x ≈ x*
  σᵏ*x≈x* = σ-convergesTo-x* x∈B₀

  -- Proofs

  σᵏx∈B₀ : ∀ k → σ k x ∈ᵢ B₀
  σᵏx∈B₀ zero    = x∈B₀
  σᵏx∈B₀ (suc K) = B-closed (σᵏx∈B₀ K)
  
  σ-mono : ∀ {k t} → k ≤ t → σ t x ≤ₛ σ k x
  σ-mono {zero}  {zero}  z≤n       = ≤-refl
  σ-mono {zero}  {suc k} z≤n       = ≤-trans (F-decreasing (σᵏx∈B₀ k)) (σ-mono {0} {k} z≤n)
  σ-mono {suc k} {suc t} (s≤s k≤t) = F-monotone (σᵏx∈B₀ t) (σᵏx∈B₀ k) (σ-mono k≤t)

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

  x*≤x∈B₀ : x* ≤ₛ x
  x*≤x∈B₀ = x*≤σᵏx 0

  σᵏx*≈x* : ∀ k → σ k x* ≈ x*
  σᵏx*≈x* zero    = ≈-refl
  σᵏx*≈x* (suc k) = ≈-trans (F-cong (σᵏx*≈x* k)) x*-fixed


  x*∈B : x* ∈ᵢ B₀
  x*∈B = B-cong σᵏ*x≈x* (σᵏx∈B₀ k*)




-- Sequence of sets

module _ {y} (y∈B₀ : y ∈ᵢ B₀) where

  D : ℕ → IPred Sᵢ _
  D k i xᵢ = (xᵢ ∈ B₀ i) × (x* i ≤ᵢ xᵢ) × (xᵢ ≤ᵢ σ k y i)

  Dᵢ-cong : ∀ {k i} {x y : Sᵢ i} → x ≈ᵢ y → x ∈ D k i → y ∈ D k i
  Dᵢ-cong x≈y (x∈Dᵢ , x*ᵢ≤x , x≤σᵏyᵢ) =
    Bᵢ-cong x≈y x∈Dᵢ ,
    ≤ᵢ-respʳ-≈ᵢ x≈y x*ᵢ≤x ,
    ≤ᵢ-respˡ-≈ᵢ x≈y x≤σᵏyᵢ

  F-resp-D₀ : ∀ {x} → x ∈ᵢ D 0 → F x ∈ᵢ D 0
  F-resp-D₀ x∈D₀ i =
    B-closed x∈D i ,
    x*≤σᵏx x∈D 1 i ,
    ≤ᵢ-trans (F-decreasing x∈D i) ((proj₂ ∘ proj₂ ∘ x∈D₀) i)
    where x∈D = proj₁ ∘ x∈D₀

  D-finish₁ : ∀ k → x* ∈ᵢ D k
  D-finish₁ k i = x*∈B y∈B₀ i , ≤ᵢ-refl , x*≤σᵏx y∈B₀ k i

  D-finish₂ : ∀ {k} → k* ≤ k → ∀ {x} → x ∈ᵢ D k → x ≈ x*
  D-finish₂ k*≤k x∈Dₖ i with x∈Dₖ i
  ... | (_ , x*ᵢ≤xᵢ , xᵢ≤σᵏxᵢ) =
    ≤ᵢ-antisym (≤ᵢ-trans xᵢ≤σᵏxᵢ (≤ᵢ-reflexive (σ-fixed y∈B₀ k*≤k i) )) x*ᵢ≤xᵢ

  D-finish : ∀ {k} → k* ≤ k → Singletonᵢ _≈_ (D k) x*
  D-finish {k} k*≤k = D-finish₁ k , D-finish₂ k*≤k

  F-mono-D  : ∀ {k x} → x ∈ᵢ D k → F x ∈ᵢ D (suc k)
  F-mono-D {k} {x} x∈Dₖ i =
    B-closed x∈D i ,
    x*≤σᵏx x∈D 1 i ,
    F-monotone x∈D (σᵏx∈B₀ y∈B₀ k) (proj₂ ∘ proj₂ ∘ x∈Dₖ) i
    where x∈D = proj₁ ∘ x∈Dₖ

  y∈D₀ : y ∈ᵢ D 0
  y∈D₀ i = y∈B₀ i , x*≤x∈B₀ y∈B₀ i , ≤ᵢ-refl
  
  aco : PartialACO I∥ (D 0) _
  aco = record
    { B         = D
    ; X₀≋B₀     = ≋ᵢ-refl
    ; Bᵢ-cong   = λ {k} → Dᵢ-cong {k}
    ; F-resp-B₀ = F-resp-D₀
    ; F-mono-B  = λ {k} → F-mono-D {k}
    ; x*        = x*
    ; k*        = k*
    ; B-finish  = D-finish
    }

{-
module NonDependent where

  D : ℕ → IPred Sᵢ _
  D k i xᵢ = (xᵢ ∈ D i) × (x* i ≤ᵢ xᵢ) × (∃ λ y → y ∈ᵢ D × xᵢ ≤ᵢ σ k y i × (∀ y' ∈)

  Dᵢ-cong : ∀ {k i} {x y : Sᵢ i} → x ≈ᵢ y → x ∈ D k i → y ∈ D k i
  Dᵢ-cong x≈y (x∈Dᵢ , x*ᵢ≤x , y , y∈D , x≤σᵏyᵢ) =
    Dᵢ-cong x≈y x∈Dᵢ ,
    ≤ᵢ-respʳ-≈ᵢ x≈y x*ᵢ≤x ,
    (y , y∈D , ≤ᵢ-respˡ-≈ᵢ x≈y x≤σᵏyᵢ)

  F-resp-D₀ : ∀ {x} → x ∈ᵢ D 0 → F x ∈ᵢ D 0
  F-resp-D₀ x∈D₀ i =
    D-closed x∈D i ,
    x*≤σᵏx x∈D 1 i ,
    y , y∈D , ≤ᵢ-trans (F-decreasing x∈D i) xᵢ≤σᵏyᵢ
    where
    x∈D     = proj₁ ∘ x∈D₀
    y       = (proj₁ ∘ proj₂ ∘ proj₂ ∘ x∈D₀) i
    y∈D     = (proj₁ ∘ proj₂ ∘ proj₂ ∘ proj₂ ∘ x∈D₀) i
    xᵢ≤σᵏyᵢ = (proj₂ ∘ proj₂ ∘ proj₂ ∘ proj₂ ∘ x∈D₀) i


  D-finish₁ : ∀ k → x* ∈ᵢ D k
  D-finish₁ k i = x*∈D i , ≤ᵢ-refl , x* , x*∈D , ≤ᵢ-reflexive (≈ᵢ-sym (σᵏx*≈x* x*∈D k i))

  D-finish₂ : ∀ {k} → k* ≤ k → ∀ {x} → x ∈ᵢ D k → x ≈ x*
  D-finish₂ k*≤k x∈Dₖ i with x∈Dₖ i
  ... | (xᵢ∈Dᵢ , x*ᵢ≤xᵢ , y , y∈D , xᵢ≤σᵏxᵢ) =
    ≤ᵢ-antisym (≤ᵢ-trans xᵢ≤σᵏxᵢ (≤ᵢ-reflexive (σ-fixed y∈D k*≤k i) )) x*ᵢ≤xᵢ
    where
    x*≤x = proj₁ ∘ proj₂ ∘ x∈Dₖ
    x≤σᵏ = proj₂ ∘ proj₂ ∘ x∈Dₖ

  D-finish : ∀ {k} → k* ≤ k → Singletonᵢ _≈_ (D k) x*
  D-finish {k} k*≤k = D-finish₁ k , D-finish₂ k*≤k

  F-mono-D  : ∀ {k x} → x ∈ᵢ D k → F x ∈ᵢ D (suc k)
  F-mono-D {k} {x} x∈Dₖ i =
    D-closed x∈D i ,
    ≤-respˡ-≈ x*-fixed (F-monotone x*∈D x∈D x*≤x) i ,
    y , y∈D , F-monotone x∈D (σᵏx∈D y∈D k) x≤σᵏy i
    where
    x∈D    = proj₁ ∘ x∈Dₖ
    x*≤x   = proj₁ ∘ proj₂ ∘ x∈Dₖ
    y      = λ i → (proj₁ ∘ proj₂ ∘ proj₂ ∘ x∈Dₖ) i i
    y∈D    = λ i → (proj₁ ∘ proj₂ ∘ proj₂ ∘ proj₂ ∘ x∈Dₖ) i i

    x≤σᵏy : x ≤ₛ σ k y
    x≤σᵏy j = {!!} --λ i → (proj₂ ∘ proj₂ ∘ proj₂ ∘ proj₂ ∘ x∈Dₖ) i

  D₀⊆D : ∀ {x} → x ∈ᵢ D 0 → x ∈ᵢ D
  D₀⊆D x∈D = proj₁ ∘ x∈D

  D⊆D₀ : ∀ {x} → x ∈ᵢ D → x ∈ᵢ D 0
  D⊆D₀ {x} x∈D i = x∈D i , x*≤x∈D x∈D i , x , x∈D , ≤ᵢ-refl

  aco : PartialACO I∥ D _
  aco = record
    { D         = D
    ; Dᵢ-cong   = λ {k} → Dᵢ-cong {k}
    ; F-resp-D₀ = F-resp-D₀
    ; F-mono-D  = λ {k} → F-mono-D {k}
    ; x*        = x*
    ; k*        = k*
    ; D-finish  = D-finish
    ; X₀≋D₀     = {!!}
    }
-}
