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

open import RoutingLib.Relation.Unary.Indexed

open import RoutingLib.Iteration.Asynchronous.Static
open import RoutingLib.Iteration.Asynchronous.Static.Convergence.Conditions

module RoutingLib.Iteration.Asynchronous.Static.Convergence.SyncImpliesACO
  {a ℓ n p o} (I∥ : AsyncIterable a ℓ n)
  {D : IPred _ p} (sync : PartialSynchronousConditions I∥ D o)
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

open import RoutingLib.Iteration.Synchronous using (_^_)

open AsyncIterable I∥
open PartialSynchronousConditions sync

σ : ℕ → S → S
σ k = (F ^ k)

--------------------------------------------------------------------------------
-- Proof
  
module _ {x} (x∈D : x ∈ᵢ D) where

  σᵏ*x≈x* : σ k* x ≈ x*
  σᵏ*x≈x* = σ-convergesTo-x* x∈D

  -- Proofs

  σᵏx∈D : ∀ k → σ k x ∈ᵢ D
  σᵏx∈D zero    = x∈D
  σᵏx∈D (suc K) = D-closed (σᵏx∈D K)
  
  σ-mono : ∀ {k t} → k ≤ t → σ t x ≤ₛ σ k x
  σ-mono {zero}  {zero}  z≤n       = ≤-refl
  σ-mono {zero}  {suc k} z≤n       = ≤-trans (F-decreasing (σᵏx∈D k)) (σ-mono {0} {k} z≤n)
  σ-mono {suc k} {suc t} (s≤s k≤t) = F-monotone (σᵏx∈D t) (σᵏx∈D k) (σ-mono k≤t)

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

  x*≤x∈D : x* ≤ₛ x
  x*≤x∈D = x*≤σᵏx 0

  σᵏx*≈x* : ∀ k → σ k x* ≈ x*
  σᵏx*≈x* zero    = ≈-refl
  σᵏx*≈x* (suc k) = ≈-trans (F-cong (σᵏx*≈x* k)) x*-fixed


  x*∈D : x* ∈ᵢ D
  x*∈D = D-cong σᵏ*x≈x* (σᵏx∈D k*)




-- Sequence of sets

module _ {y} (y∈D : y ∈ᵢ D) where

  B : ℕ → IPred Sᵢ _
  B k i xᵢ = (xᵢ ∈ D i) × (x* i ≤ᵢ xᵢ) × (xᵢ ≤ᵢ σ k y i)

  Bᵢ-cong : ∀ {k i} {x y : Sᵢ i} → x ≈ᵢ y → x ∈ B k i → y ∈ B k i
  Bᵢ-cong x≈y (x∈Bᵢ , x*ᵢ≤x , x≤σᵏyᵢ) =
    Dᵢ-cong x≈y x∈Bᵢ ,
    ≤ᵢ-respʳ-≈ᵢ x≈y x*ᵢ≤x ,
    ≤ᵢ-respˡ-≈ᵢ x≈y x≤σᵏyᵢ

  F-resp-B₀ : ∀ {x} → x ∈ᵢ B 0 → F x ∈ᵢ B 0
  F-resp-B₀ x∈B₀ i =
    D-closed x∈D i ,
    x*≤σᵏx x∈D 1 i ,
    ≤ᵢ-trans (F-decreasing x∈D i) ((proj₂ ∘ proj₂ ∘ x∈B₀) i)
    where x∈D = proj₁ ∘ x∈B₀

  B-finish₁ : ∀ k → x* ∈ᵢ B k
  B-finish₁ k i = x*∈D y∈D i , ≤ᵢ-refl , x*≤σᵏx y∈D k i

  B-finish₂ : ∀ {k} → k* ≤ k → ∀ {x} → x ∈ᵢ B k → x ≈ x*
  B-finish₂ k*≤k x∈Dₖ i with x∈Dₖ i
  ... | (_ , x*ᵢ≤xᵢ , xᵢ≤σᵏxᵢ) =
    ≤ᵢ-antisym (≤ᵢ-trans xᵢ≤σᵏxᵢ (≤ᵢ-reflexive (σ-fixed y∈D k*≤k i) )) x*ᵢ≤xᵢ

  B-finish : ∀ {k} → k* ≤ k → Singletonᵢ _≈_ (B k) x*
  B-finish {k} k*≤k = B-finish₁ k , B-finish₂ k*≤k

  F-mono-B  : ∀ {k x} → x ∈ᵢ B k → F x ∈ᵢ B (suc k)
  F-mono-B {k} {x} x∈Bₖ i =
    D-closed x∈D i ,
    x*≤σᵏx x∈D 1 i ,
    F-monotone x∈D (σᵏx∈D y∈D k) (proj₂ ∘ proj₂ ∘ x∈Bₖ) i
    where x∈D = proj₁ ∘ x∈Bₖ

  y∈B₀ : y ∈ᵢ B 0
  y∈B₀ i = y∈D i , x*≤x∈D y∈D i , ≤ᵢ-refl
  
  aco : PartialACO I∥ (B 0) _
  aco = record
    { D         = B
    ; X₀≋D₀     = ≋ᵢ-refl
    ; Dᵢ-cong   = λ {k} → Bᵢ-cong {k}
    ; F-resp-D₀ = F-resp-B₀
    ; F-mono-D  = λ {k} → F-mono-B {k}
    ; x*        = x*
    ; k*        = k*
    ; D-finish  = B-finish
    }

{-
module NonDependent where

  B : ℕ → IPred Sᵢ _
  B k i xᵢ = (xᵢ ∈ D i) × (x* i ≤ᵢ xᵢ) × (∃ λ y → y ∈ᵢ D × xᵢ ≤ᵢ σ k y i × (∀ y' ∈)

  Bᵢ-cong : ∀ {k i} {x y : Sᵢ i} → x ≈ᵢ y → x ∈ B k i → y ∈ B k i
  Bᵢ-cong x≈y (x∈Dᵢ , x*ᵢ≤x , y , y∈D , x≤σᵏyᵢ) =
    Dᵢ-cong x≈y x∈Dᵢ ,
    ≤ᵢ-respʳ-≈ᵢ x≈y x*ᵢ≤x ,
    (y , y∈D , ≤ᵢ-respˡ-≈ᵢ x≈y x≤σᵏyᵢ)

  F-resp-B₀ : ∀ {x} → x ∈ᵢ B 0 → F x ∈ᵢ B 0
  F-resp-B₀ x∈D₀ i =
    D-closed x∈D i ,
    x*≤σᵏx x∈D 1 i ,
    y , y∈B , ≤ᵢ-trans (F-decreasing x∈D i) xᵢ≤σᵏyᵢ
    where
    x∈D     = proj₁ ∘ x∈D₀
    y       = (proj₁ ∘ proj₂ ∘ proj₂ ∘ x∈D₀) i
    y∈B     = (proj₁ ∘ proj₂ ∘ proj₂ ∘ proj₂ ∘ x∈D₀) i
    xᵢ≤σᵏyᵢ = (proj₂ ∘ proj₂ ∘ proj₂ ∘ proj₂ ∘ x∈D₀) i


  B-finish₁ : ∀ k → x* ∈ᵢ B k
  B-finish₁ k i = x*∈D i , ≤ᵢ-refl , x* , x*∈D , ≤ᵢ-reflexive (≈ᵢ-sym (σᵏx*≈x* x*∈D k i))

  B-finish₂ : ∀ {k} → k* ≤ k → ∀ {x} → x ∈ᵢ B k → x ≈ x*
  B-finish₂ k*≤k x∈Dₖ i with x∈Dₖ i
  ... | (xᵢ∈Bᵢ , x*ᵢ≤xᵢ , y , y∈B , xᵢ≤σᵏxᵢ) =
    ≤ᵢ-antisym (≤ᵢ-trans xᵢ≤σᵏxᵢ (≤ᵢ-reflexive (σ-fixed y∈B k*≤k i) )) x*ᵢ≤xᵢ
    where
    x*≤x = proj₁ ∘ proj₂ ∘ x∈Dₖ
    x≤σᵏ = proj₂ ∘ proj₂ ∘ x∈Dₖ

  B-finish : ∀ {k} → k* ≤ k → Singletonᵢ _≈_ (B k) x*
  B-finish {k} k*≤k = B-finish₁ k , B-finish₂ k*≤k

  F-mono-B  : ∀ {k x} → x ∈ᵢ B k → F x ∈ᵢ B (suc k)
  F-mono-B {k} {x} x∈Dₖ i =
    D-closed x∈B i ,
    ≤-respˡ-≈ x*-fixed (F-monotone x*∈D x∈B x*≤x) i ,
    y , y∈B , F-monotone x∈B (σᵏx∈D y∈B k) x≤σᵏy i
    where
    x∈B    = proj₁ ∘ x∈Dₖ
    x*≤x   = proj₁ ∘ proj₂ ∘ x∈Dₖ
    y      = λ i → (proj₁ ∘ proj₂ ∘ proj₂ ∘ x∈Dₖ) i i
    y∈B    = λ i → (proj₁ ∘ proj₂ ∘ proj₂ ∘ proj₂ ∘ x∈Dₖ) i i

    x≤σᵏy : x ≤ₛ σ k y
    x≤σᵏy j = {!!} --λ i → (proj₂ ∘ proj₂ ∘ proj₂ ∘ proj₂ ∘ x∈Dₖ) i

  D₀⊆B : ∀ {x} → x ∈ᵢ B 0 → x ∈ᵢ D
  D₀⊆B x∈D = proj₁ ∘ x∈D

  B⊆D₀ : ∀ {x} → x ∈ᵢ D → x ∈ᵢ B 0
  B⊆D₀ {x} x∈B i = x∈B i , x*≤x∈D x∈B i , x , x∈B , ≤ᵢ-refl

  aco : PartialACO I∥ D _
  aco = record
    { D         = B
    ; Dᵢ-cong   = λ {k} → Bᵢ-cong {k}
    ; F-resp-D₀ = F-resp-B₀
    ; F-mono-D  = λ {k} → F-mono-B {k}
    ; x*        = x*
    ; k*        = k*
    ; D-finish  = B-finish
    ; X₀≋D₀     = {!!}
    }
-}
