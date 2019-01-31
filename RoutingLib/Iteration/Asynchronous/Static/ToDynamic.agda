------------------------------------------------------------------------
-- This module shows that a static asynchronous iteration is merely a
-- special type of a dynamic asynchronous iteration, and therefore
-- convergence (and the associated pre-conditions) can be converted to
-- dynamic iterations and then back again.
------------------------------------------------------------------------

import RoutingLib.Iteration.Asynchronous.Static as Static

module RoutingLib.Iteration.Asynchronous.Static.ToDynamic
  {a ℓ n} (I∥ : Static.AsyncIterable a ℓ n) where

open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (all?)
open import Data.Fin.Subset using (Subset; _∉_) renaming (⊤ to ⊤ₛ; _∈_ to _∈ₛ_)
open import Data.Fin.Subset.Properties using (_∈?_; ∈⊤)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _<_; _≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Maybe using (Maybe; just; nothing; to-witness; Is-just)
open import Data.Unit using (⊤; tt)
open import Data.Product using (∃; ∃₂; _,_; _×_; proj₁; proj₂)
open import Function using (_∘_)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using (<-wellFounded)
open import Level using (lift; _⊔_)
open import Relation.Binary using (Rel; _Respects_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.Indexed.Homogeneous hiding (Rel; Lift)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred; U; _∈_)
import Relation.Binary.EqReasoning as EqReasoning

open import RoutingLib.Data.Fin.Subset using (Full)
open import RoutingLib.Data.Fin.Subset.Properties using (⊤-full)
open import RoutingLib.Data.Maybe.Properties
open import RoutingLib.Relation.Unary.Indexed using (IPred; _∈ᵢ_; _⊆ᵢ_; _≋ᵢ_)
open import RoutingLib.Relation.Unary.Indexed.Construct.Add.Point.Exclude
import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.FiniteSubset as FiniteSubset
open import RoutingLib.Relation.Nullary.Indexed.Construct.Add.Point
import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.Add.Point.Equality.DecSetoid
  as LiftedEquality
open import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.At using (_atₛ_)

import RoutingLib.Iteration.Asynchronous.Dynamic as Dynamic
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions as Dynamic
import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule as Dynamic
import RoutingLib.Iteration.Asynchronous.Static.Schedule as Static
open import RoutingLib.Iteration.Asynchronous.Static.Schedule.Construct.Synchronous
import RoutingLib.Iteration.Asynchronous.Static.Schedule.Pseudoperiod as Static
import RoutingLib.Iteration.Asynchronous.Static.Convergence.Conditions as Static
open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule
  using (Epoch; 𝕋) renaming ([_,_] to [_,_]ₜ)
open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule.FromStatic

open Static.AsyncIterable I∥

------------------------------------------------------------------------
-- Formulating the dynamic iteration
------------------------------------------------------------------------
-- First it is neccessary to include an ``extra`` invalid state
-- and equality is lifted pointwise in the obvious way

S∙ᵢ : Fin n → Set a
S∙ᵢ = Pointedᵢ Sᵢ

S∙ : Set a
S∙ = ∀ i → S∙ᵢ i

open LiftedEquality ≈-iDecSetoid public
open FiniteSubset S∙ᵢ _≈∙ᵢ_ using () renaming (_∼[_]_ to _≈∙[_]_) public

------------------------------------------------------------------------
-- The iteration can then be lifted as well

F∙ : Epoch → Subset n → S∙ → S∙
F∙ e p x i with all? (IsJust? ∘ x)
... | yes xᵥ = just (F (to-witness ∘ xᵥ) i)
... | no  _  = nothing

F∙-cong : ∀ e p {x y} → (∀ i → x i ≈∙ᵢ y i) → F∙ e p x ≈∙[ p ] F∙ e p y
F∙-cong e p {x} {y} x≈y {i} i∈p with all? (IsJust? ∘ x) | all? (IsJust? ∘ y)
... | yes xᵥ | yes yᵥ = [ F-cong (λ j → extractValueᵢ-cong (x≈y j) (xᵥ j) (yᵥ j)) i ]ᵢ
... | yes xᵥ | no ¬yᵥ = contradiction (IsValue-resp-≈∙ x≈y xᵥ) ¬yᵥ
... | no ¬xᵥ | yes yᵥ = contradiction (IsValue-resp-≈∙ (≈∙-sym x≈y) yᵥ) ¬xᵥ
... | no  _  | no  _  = ∙≈ᵢ∙

F∙-isAsyncIterable : Dynamic.IsAsyncIterable _≈∙ᵢ_ F∙ ∙
F∙-isAsyncIterable = record
  { isDecEquivalenceᵢ = ≈∙ᵢ-isIDecEquivalence
  ; F-cong            = F∙-cong
  }

I∙∥ : Dynamic.AsyncIterable a (a ⊔ ℓ) n
I∙∥ = record
  { isAsyncIterable = F∙-isAsyncIterable
  }

------------------------------------------------------------------------
-- The dynamic iteration mirrors the static iteration

module _ (ψ : Static.Schedule n) where

  open Static.Schedule ψ

  F-sim : ∀ x i → [ F x i ]ᵢ ≈∙ᵢ F∙ 0 ⊤ₛ [ x ] i
  F-sim x i with all? (IsJust? ∘ [ x ])
  ... | yes [x]ᵥ  = [ F-cong ([≈]-injective (extract-IsValue [x]ᵥ)) i ]ᵢ
  ... | no  ¬[x]ᵥ = contradiction (λ _ → [ tt ]ᵢ) ¬[x]ᵥ

  asyncIter-sim : ∀ x₀ {t} (accₜ : Acc _<_ t) →
                  [ Static.asyncIter' I∥ ψ x₀ accₜ ] ≈∙
                  Dynamic.asyncIter' I∙∥ (convert ψ) [ x₀ ] accₜ
  asyncIter-sim x₀ {zero} rec i with i ∈? ⊤ₛ
  ... | yes _   = ≈∙ᵢ-refl
  ... | no  i∉⊤ = contradiction ∈⊤ i∉⊤
  asyncIter-sim x₀ {suc t} (acc rec) i with i ∈? ⊤ₛ | i ∈? α (suc t)
  ... | no  i∉⊤ | _     = contradiction ∈⊤ i∉⊤
  ... | yes _   | no  _ = asyncIter-sim x₀ (rec t _) i
  ... | yes _   | yes _ = begin
    [ F (λ j → Static.asyncIter' I∥ ψ x₀ (rec (β (suc t) i j) _) j) i ]ᵢ      ≈⟨ F-sim _ i ⟩
    F∙ 0 ⊤ₛ (λ j → [ Static.asyncIter' I∥ ψ x₀ (rec (β (suc t) i j) _) ] j) i ≈⟨ F∙-cong 0 ⊤ₛ (λ j → asyncIter-sim x₀ (rec (β (suc t) i j) _) j) ∈⊤ ⟩
    F∙ 0 ⊤ₛ (λ j → Dynamic.asyncIter' I∙∥ (convert ψ) [ x₀ ] (rec (β (suc t) i j) _) j) i ∎
    where open EqReasoning (≈∙-setoidᵢ atₛ i)

------------------------------------------------------------------------
-- If the dynamic iteration converges then the static iteration
-- converges

module DynamicToStaticConvergence
  (C : Dynamic.PartiallyConvergent I∙∥ (λ i → IsValueᵢ) Full)
  (x : S)  -- The set of states must be non-empty to prove this result
  where

  open Dynamic.PartiallyConvergent C

  x*∙ : S∙
  x*∙ = x* 0 ⊤-full

  k*∙ : 𝕋
  k*∙ = k* 0 ⊤-full

  x*∙-isValue : IsValue x*∙
  x*∙-isValue = IsValue-resp-≈∙ δ≈x* IsValue[ _ ]
    where
    open EqReasoning ≈∙-setoid
    δ≈x* : [ Static.asyncIter I∥ ψˢʸⁿᶜ x k*∙ ] ≈∙ x*∙
    δ≈x* = begin
      [ Static.asyncIter I∥ ψˢʸⁿᶜ x k*∙ ]             ≈⟨ asyncIter-sim ψˢʸⁿᶜ x (<-wellFounded k*∙) ⟩
      Dynamic.asyncIter I∙∥ dψˢʸⁿᶜ [ x ] k*∙          ≈⟨ x*-reached IsValue[ x ] (λ _ → ⊤-full) {tₛ = 0} dψˢʸⁿᶜ-mpp dψˢʸⁿᶜ-η[k*∙,k*∙] ⟩
      x*∙                                           ∎
      where
      dψˢʸⁿᶜ            = convert ψˢʸⁿᶜ
      dψˢʸⁿᶜ-η[k*∙,k*∙] = convert-subEpoch ψˢʸⁿᶜ {k*∙} {k*∙} ≤-refl
      dψˢʸⁿᶜ-mpp        = convert-multiPseudoperiod ψˢʸⁿᶜ (ψˢʸⁿᶜ-multiPseudoperiodic 0 k*∙)

  x*ₛ : S
  x*ₛ = extractValue (x*∙-isValue)

  x*ₛ-fixed : F x*ₛ ≈ x*ₛ
  x*ₛ-fixed i with x*-fixed 0 ⊤-full
  ... | F∙x*≈x* with all? (IsJust? ∘ (x* 0 ⊤-full))
  ...   | no ¬x*∙ᵥ = contradiction x*∙-isValue ¬x*∙ᵥ
  ...   | yes x*∙ᵥ = begin
    F x*ₛ                        i ≡⟨⟩
    F (extractValue x*∙-isValue) i ≈⟨ F-cong (extractValue-cong ≈∙-refl x*∙-isValue x*∙ᵥ) i ⟩
    F (extractValue x*∙ᵥ)        i ≈⟨ [≈]ᵢ-injective (≈∙ᵢ-trans (F∙x*≈x* i) (extract-IsValueᵢ (x*∙-isValue i))) ⟩
    x*ₛ                          i ∎
    where
    open EqReasoning (≈ᵢ-iSetoid atₛ i)

  k*ₛ : ℕ
  k*ₛ = k* 0 ⊤-full

  x*ₛ-reached : ∀ {x₀ : S} → x₀ ∈ U →
                ∀ (ψ : Static.Schedule n) {s m e : 𝕋} →
                Static.IsMultiPseudoperiodic ψ k*ₛ [ s , m ]ₜ →
                m ≤ e →
                Static.asyncIter I∥ ψ x₀ e ≈ x*ₛ
  x*ₛ-reached {x₀} _ ψ {e = e} mpp m≤e = [≈]-injective (begin
    [ Static.asyncIter I∥ ψ x₀ e   ]  ≈⟨ asyncIter-sim ψ x₀ (<-wellFounded e) ⟩
    Dynamic.asyncIter I∙∥ ψᵈ [ x₀ ] e ≈⟨ x*-reached IsValue[ x₀ ] ψᵈ-full ψᵈ-mpp ψᵈ-η[m,e] ⟩
    x*∙                              ≈⟨ extract-IsValue x*∙-isValue ⟩
    [ x*ₛ ]                          ∎)
    where
    open EqReasoning ≈∙-setoid
    ψᵈ        = convert ψ
    ψᵈ-full   = convert∈Full ψ
    ψᵈ-mpp    = convert-multiPseudoperiod ψ mpp
    ψᵈ-η[m,e] = convert-subEpoch ψ m≤e

  dynamicToStaticConvergence : Static.Converges I∥
  dynamicToStaticConvergence = record
    { x*         = x*ₛ
    ; k*         = k*ₛ
    ; x*-fixed   = x*ₛ-fixed
    ; x*-reached = x*ₛ-reached
    }

open DynamicToStaticConvergence public using (dynamicToStaticConvergence)

------------------------------------------------------------------------
-- Translation from static ACO to a dynamic ACO

module StaticToDynamicACO {ℓ} (aco : Static.ACO I∥ ℓ) where

  open Static.ACO aco
  open Dynamic.AsyncIterable using (Accordant)

  -- Initial box
  B∙₀ : IPred S∙ᵢ ℓ
  B∙₀ = Lift∙ (B 0)

  B∙₀-cong : ∀ {x y} → x ≈∙ y → x ∈ᵢ B∙₀ → y ∈ᵢ B∙₀
  B∙₀-cong = Lift∙-cong Bᵢ-cong

  F∙-resp-B∙₀ : ∀ {e p} (p∈F : p ∈ Full) → ∀ {x} → x ∈ᵢ B∙₀ → F∙ e p x ∈ᵢ B∙₀
  F∙-resp-B∙₀ {e} {p} p∈F {x} x∈B∙₀ i with all? (IsJust? ∘ x)
  ... | no ¬xᵥ = contradiction (∈-isValue x∈B∙₀) ¬xᵥ
  ... | yes xᵥ = F-resp-B₀ (∈-extractValue xᵥ x∈B∙₀) i


  -- Main boxes
  B∙ : Epoch → {p : Subset n} → p ∈ Full → ℕ → IPred S∙ᵢ ℓ
  B∙ e p k = Lift∙ (B k)

  B∙₀⊆B∙₀ₑ : ∀ e {p} (p∈F : p ∈ Full) → B∙₀ ⊆ᵢ B∙ e p∈F 0
  B∙₀⊆B∙₀ₑ e p∈F {i} {∙ᵢ}     ()
  B∙₀⊆B∙₀ₑ e p∈F {i} {[ xᵢ ]ᵢ} x∈B₀ = x∈B₀

  B∙₀ₑ⊆B∙₀ : ∀ e {p} (p∈F : p ∈ Full) → B∙ e p∈F 0 ⊆ᵢ B∙₀
  B∙₀ₑ⊆B∙₀ e p∈F {i} {∙ᵢ}     ()
  B∙₀ₑ⊆B∙₀ e p∈F {i} {[ xᵢ ]ᵢ} x∈B₀ = x∈B₀

  B∙₀-eqᵢ : ∀ {e p} (p∈F : p ∈ Full) → B∙₀ ≋ᵢ B∙ e p∈F 0
  B∙₀-eqᵢ {e} p∈F = (λ {i xᵢ} → B∙₀⊆B∙₀ₑ e p∈F {i} {xᵢ}) , (λ {i xᵢ} → B∙₀ₑ⊆B∙₀ e p∈F {i} {xᵢ})

  B∙ᵢ-cong  : ∀ {e f : ℕ} {p q : Subset n} → e ≡ f → p ≡ q →
              (p∈Q : p ∈ Full) (q∈Q : q ∈ Full) {k : ℕ} {i : Fin n}
              {x y : Pointedᵢ Sᵢ i} →
              x ≈∙ᵢ y → x ∈ Lift∙ (B k) i → y ∈ Lift∙ (B k) i
  B∙ᵢ-cong refl refl p∈F q∈F = Lift∙-congᵢ Bᵢ-cong

  B∙-finish : ∀ e {p} (p∈F : p ∈ Full) → ∃₂ (λ k* x* →
                ∀ {k} → k* ≤ k →
                  (x* ∈ᵢ B∙ e p∈F k) ×
                  (∀ {x} → x ∈ᵢ B∙ e p∈F k → x ≈∙ x*))
  B∙-finish e p with B-finish
  ... | k* , x* , res = k* , [ x* ] , λ k*≤k → x*∈B∙ₖ k*≤k , x∈B∙ₖ⇒x≈x* k*≤k
    where
    x*∈B∙ₖ : ∀ {k} → k* ≤ k → [ x* ] ∈ᵢ B∙ e p k
    x*∈B∙ₖ k*≤k = proj₁ (res k*≤k)

    x∈B∙ₖ⇒x≈x* : ∀ {k} → k* ≤ k → ∀ {x} → x ∈ᵢ B∙ e p k → x ≈∙ [ x* ]
    x∈B∙ₖ⇒x≈x* {k} k*≤k {x} x∈B∙ₑₚₖ = begin
      x                   ≈⟨ extract-IsValue xᵥ ⟩
      [ extractValue xᵥ ] ≈⟨ [ proj₂ (res k*≤k) (∈-extractValue xᵥ x∈B∙ₑₚₖ) ]≈ ⟩
      [ x*              ] ∎
      where
      open EqReasoning ≈∙-setoid

      xᵥ : IsValue x
      xᵥ = ∈-isValue x∈B∙ₑₚₖ

  B∙-null : ∀ {e p} (p∈F : p ∈ Full) → ∀ {k i} → i ∉ p → ∙ᵢ ∈ B∙ e p∈F k i
  B∙-null _∈p {i = i} i∉p = contradiction (i ∈p) i∉p

  F∙-mono-B∙ : ∀ {e p} (p∈F : p ∈ Full) {k x} → x ∈ Accordant I∙∥ p →
               x ∈ᵢ B∙ e p∈F k → F∙ e p x ∈ᵢ B∙ e p∈F (suc k)
  F∙-mono-B∙ {e} {p} p∈F {x = x} x-wf x∈B∙ₖ i with all? (IsJust? ∘ x)
  ... | no ¬xᵥ = contradiction (∈-isValue x∈B∙ₖ) ¬xᵥ
  ... | yes xᵥ = F-mono-B (∈-extractValue xᵥ x∈B∙ₖ) i

  staticToDynamicACO : Dynamic.PartialACO I∙∥ B∙₀ Full ℓ
  staticToDynamicACO = record
    { B₀-cong   = B∙₀-cong
    ; F-resp-B₀ = λ {e} → F∙-resp-B∙₀ {e}
    ; B         = B∙
    ; B₀-eqᵢ    = λ {e} → B∙₀-eqᵢ {e}
    ; Bᵢ-cong   = λ {e} → B∙ᵢ-cong {e}
    ; B-finish  = B∙-finish
    ; B-null    = λ {e} → B∙-null {e}
    ; F-mono-B  = λ {e} → F∙-mono-B∙ {e}
    }

open StaticToDynamicACO public using (staticToDynamicACO; B∙₀)

------------------------------------------------------------------------
-- Translation from static AMCO to a dynamic AMCO
