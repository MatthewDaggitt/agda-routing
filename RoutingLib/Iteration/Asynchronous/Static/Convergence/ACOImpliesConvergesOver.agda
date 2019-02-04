--------------------------------------------------------------------------
-- A proof that F being an ACO implies that the iteration converges over
-- the initial box. The same result is also derived in
-- `RoutingLib.Iteration.Asynchronous.Static.ToDynamic` by going via
-- dynamic iterations. This version of the proof is included for the
-- JAR 2019 paper submission.
--
-- It's also instructive to compare this with the dynamic proof in
-- `RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.ACOImpliesConvergent`
-- in order to appreciate how the addition of epochs and participants
-- complicate the proofs.
--------------------------------------------------------------------------

open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; ⊤) renaming (_∈_ to _∈ₛ_; _∉_ to _∉ₛ_)
open import Data.Fin.Dec using (_∈?_)
open import Data.Maybe using (just; nothing)
open import Data.Nat renaming (_≟_ to _≟ℕ_) hiding (_⊔_)
open import Data.Nat.Properties hiding (_≟_)
open import Data.Product as Prod using (∃; proj₂; proj₁; _,_; _×_; map)
open import Function using (id; _∘_; _$_)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using (<-wellFounded)
open import Level using (_⊔_)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality
  using (_≡_; subst; subst₂; cong; cong₂; refl; sym; trans)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred; _⊆_; _∈_)

open import RoutingLib.Relation.Binary.Indexed.Homogeneous
open import RoutingLib.Relation.Unary.Indexed
open import RoutingLib.Relation.Unary.Properties
open import RoutingLib.Function
open import RoutingLib.Function.Reasoning

open import RoutingLib.Iteration.Asynchronous.Static
open import RoutingLib.Iteration.Asynchronous.Static.Convergence.Conditions
open import RoutingLib.Iteration.Asynchronous.Static.Schedule
import RoutingLib.Iteration.Asynchronous.Static.Schedule.Pseudoperiod
  as Pseudoperiod


module RoutingLib.Iteration.Asynchronous.Static.Convergence.ACOImpliesConvergesOver
  {a ℓ ℓ₃ n}
  (I∥ : AsyncIterable a ℓ n)
  (aco : ACO I∥ ℓ₃)
   where

open AsyncIterable I∥
open ACO  aco
-- open ACOProperties I∥ aco


k* : ℕ
k* = proj₁ (B-finish)

x* : S
x* = proj₁ (proj₂ B-finish)

B* : x*   ∈ᵢ B k* 
B* = proj₁ (proj₂ (proj₂ B-finish) ≤-refl)

F* : (F x* ∈ᵢ B (suc k*)) → F x* ≈ x* 
F* = proj₂ (proj₂ (proj₂ B-finish) (n≤1+n k*))

x*-fixed : F x* ≈ x*
x*-fixed = begin⟨ B* ⟩
  ⇒ x*   ∈ᵢ B k*       ∴⟨ F-mono-B ⟩
  ⇒ F x* ∈ᵢ B (suc k*) ∴⟨ F* ⟩
  ⇒ F x* ≈ x*          ∎

------------------------------------------------------------------------
-- Notation

module _ {x₀ : S} (x₀∈B₀ : x₀ ∈ᵢ B 0) (𝓢 : Schedule n) where

  open Schedule 𝓢
  open Pseudoperiod 𝓢

  -- Some shorthand notation where the epoch and participant indices are
  -- replaced with a time index.

  async : ∀ {t} → Acc _<_ t → S
  async = asyncIter' I∥ 𝓢 x₀

  asyncₜ : ∀ t → {rec : Acc _<_ t} → S
  asyncₜ t {rec} = async rec

  -- The concept of being locally safe

  StateOfNode_In_AtTime_ : Fin n → IPred Sᵢ ℓ₃ → 𝕋 → Set ℓ₃
  StateOfNode i In b AtTime t = (acc : Acc _<_ t) → async acc i ∈ b i

  StateIn_AtTime_ : IPred Sᵢ ℓ₃ → 𝕋 → Set ℓ₃
  StateIn b AtTime t = ∀ i → StateOfNode i In b AtTime t

  MessagesOfNode_In_AtTime_ : Fin n → IPred Sᵢ ℓ₃ → 𝕋 → Set ℓ₃
  MessagesOfNode i In b AtTime t = ∀ {j s} → t < s → (acc : Acc _<_ (β s i j)) → async acc j ∈ b j

  MessagesIn_AtTime_ : IPred Sᵢ ℓ₃ → 𝕋 → Set ℓ₃
  MessagesIn b AtTime t = ∀ i → MessagesOfNode i In b AtTime t

  data ComputationInBox_AtTime_ : ℕ → 𝕋 → Set (ℓ₃ ⊔ ℓ) where
    zeroᵇ : ∀ {t} →
            StateIn (B 0) AtTime t →
            ComputationInBox 0 AtTime t
    sucᵇ  : ∀ {t k} →
            MessagesIn (B k) AtTime t →
            StateIn (B (suc k)) AtTime t →
            ComputationInBox (suc k) AtTime t


  c∈Bₖ⇒s∈Bₖ : ∀ {t k} → ComputationInBox k AtTime t → StateIn (B k) AtTime t
  c∈Bₖ⇒s∈Bₖ (zeroᵇ s∈Bₖ)   = s∈Bₖ
  c∈Bₖ⇒s∈Bₖ (sucᵇ  _ s∈Bₖ) = s∈Bₖ

--------------------------------------------------------------------------
-- Actual proofs
--------------------------------------------------------------------------
-- Base case: the asynchronous iteration is always in the initial box

  state∈B₀ : ∀ t → StateIn (B 0) AtTime t
  state∈B₀ zero    i (acc rec) = x₀∈B₀ i
  state∈B₀ (suc t) i (acc rec) with i ∈? α (suc t)
  ... | no  _ = state∈B₀ t i (rec t _)
  ... | yes _ = begin⟨ (λ j → state∈B₀ (β (suc t) i j) j (rec (β (suc t) i j) _)) ⟩
    ⇒ (∀ j → async (rec (β (suc t) i j) _) j ∈ B 0 j)     ∴⟨ F-resp-B₀ ◌ i ⟩
    ⇒ F (λ j → async (rec (β (suc t) i j) _) j) i ∈ B 0 i ∎

--------------------------------------------------------------------------
-- Preservation: if the asynchronous iteration is in a box, 
-- then it will still be in that box in the future.

  state-steps : ∀ {k s e} → s ≤ e →
                ComputationInBox k AtTime s →
                StateIn (B k) AtTime e
  state-steps {k}     {s} {zero}  z≤n   c∈Bₖ = c∈Bₖ⇒s∈Bₖ c∈Bₖ
  state-steps {zero}  {s} {suc e} s≤1+e c∈Bₖ i (acc rec) = state∈B₀ (suc e) i (acc rec)
  state-steps {suc k} {s} {suc e} s≤1+e c∈Bₖ@(sucᵇ m∈Bₖ _) i (acc rec) with <-cmp s (suc e)
  ... | tri≈ _ refl _      = c∈Bₖ⇒s∈Bₖ c∈Bₖ i (acc rec)
  ... | tri> _ _ s>1+e     = contradiction s≤1+e (<⇒≱ s>1+e)
  ... | tri< (s≤s s≤e) _ _ with i ∈? α (suc e)
  ...   | no  _ = state-steps s≤e c∈Bₖ i (rec e ≤-refl)
  ...   | yes _ = begin⟨ (λ j → m∈Bₖ i (s≤s s≤e) _) ⟩
    ⇒ (∀ j → asyncₜ (β (suc e) i j) j ∈ B k      j)  ∴⟨ (λ prf → F-mono-B prf i) ⟩
    ⇒ F _ i                           ∈ B (suc k) i  ∎

  message-steps : ∀ {k s e} →
                  s ≤ e →
                  MessagesIn (B k) AtTime s →
                  MessagesIn (B k) AtTime e
  message-steps s≤e m∈b i e<t recβ = m∈b i (<-transʳ s≤e e<t) recβ

--------------------------------------------------------------------------
-- Step: after one pseudoperiod the node is guaranteed to have
-- advanced at least one box

  advance-stateᵢ : ∀ {s e i k} →
                   i IsActiveIn [ s , e ] →
                   MessagesOfNode i In (B k) AtTime s →
                   StateOfNode i In (B (suc k)) AtTime e
  advance-stateᵢ {s} {zero}  {i} (mkₐᵢ m ()  z≤n   i∈αₘ)
  advance-stateᵢ {s} {suc e} {i} (mkₐᵢ m s<m m≤1+e i∈αₘ) m∈Bₖ (acc recₑ)
    with i ∈? α (suc e)
  ...   | yes _ = F-mono-B (λ j → m∈Bₖ s<1+e _) i
    where s<1+e = ≤-trans s<m m≤1+e; s≤1+e = ≤-trans (n≤1+n s) s<1+e
  ...   | no  i∉α₁₊ₑ with m ≟ℕ suc e
  ...     | yes refl  = contradiction i∈αₘ i∉α₁₊ₑ
  ...     | no  m≢1+e = advance-stateᵢ (mkₐᵢ m s<m m≤e i∈αₘ) m∈Bₖ _
    where m≤e = ≤-pred (≤∧≢⇒< m≤1+e m≢1+e)

  advance-state : ∀ {s e k} →
                  IsActivationPeriod [ s , e ] →
                  MessagesIn (B k) AtTime s →
                  StateIn (B (suc k)) AtTime e
  advance-state {s} {e} {k} (mkₐ v activeᵢ) m∈Bₖ i = advance-stateᵢ (activeᵢ i) (m∈Bₖ i)

  advance-messages : ∀ {s e k} →
                     IsExpiryPeriod [ s , e ] →
                     ComputationInBox k AtTime s →
                     MessagesIn (B k) AtTime e
  advance-messages {s} (mkₑ _ expiryᵢ) c∈Bₖ i {j} e<t recβ
    = state-steps (expiryᵢ i j e<t) c∈Bₖ j recβ

--------------------------------------------------------------------------
-- Steps : after k pseudoperiods all nodes are guaranteed to have
-- advanced at least k boxes

  messages-pp : ∀ {s e k} →
                IsPseudoperiodic [ s , e ] →
                ComputationInBox k       AtTime s →
                ComputationInBox (suc k) AtTime e
  messages-pp pp c∈Bₖ = sucᵇ m∈Bₖᵉ s∈B₁₊ₖ
    where
    open IsPseudoperiodic pp
    m∈Bₖᵐ  = advance-messages β[s,m] c∈Bₖ
    m∈Bₖᵉ  = message-steps mid≤end m∈Bₖᵐ
    s∈B₁₊ₖ = advance-state α[m,e] m∈Bₖᵐ

  messages-mpp : ∀ {s e k n} →
                 IsMultiPseudoperiodic n [ s , e ] →
                 ComputationInBox k       AtTime s →
                 ComputationInBox (n + k) AtTime e
  messages-mpp {_} {_} {_} {_}     none            c∈Bₖ = c∈Bₖ
  messages-mpp {s} {e} {k} {suc n} (next m pp mpp) c∈Bₖ = begin⟨ c∈Bₖ ⟩
    ⇒ ComputationInBox k           AtTime s ∴⟨ messages-pp pp ⟩
    ⇒ ComputationInBox (suc k)     AtTime m ∴⟨ messages-mpp mpp ⟩
    ⇒ ComputationInBox (n + suc k) AtTime e ∴⟨ subst (ComputationInBox_AtTime e) (+-suc n k) ⟩
    ⇒ ComputationInBox (suc n + k) AtTime e ∎

--------------------------------------------------------------------------
-- Convergence

  computation∈Bₖ : ∀ {s e k} →
                   IsMultiPseudoperiodic k [ s , e ] →
                   ComputationInBox k AtTime e
  computation∈Bₖ {s} {e} {zero}  none = zeroᵇ (state∈B₀ s)                 
  computation∈Bₖ {s} {e} {suc k} (next m pp mpp) = begin⟨ zeroᵇ (state∈B₀ s) ⟩
    ⇒ ComputationInBox 0       AtTime s ∴⟨ messages-pp pp ⟩
    ⇒ ComputationInBox 1       AtTime m ∴⟨ messages-mpp mpp ⟩
    ⇒ ComputationInBox (k + 1) AtTime e ∴⟨ subst (ComputationInBox_AtTime e) (+-comm k 1) ⟩
    ⇒ ComputationInBox (1 + k) AtTime e ∎

  module _ {s m e : 𝕋} where

    x*-reached : IsMultiPseudoperiodic k* [ s , m ] → m ≤ e → asyncₜ e ≈ x* 
    x*-reached mpp m≤e = begin⟨ mpp ⟩
      ⇒ IsMultiPseudoperiodic k* [ s , m ] ∴⟨ computation∈Bₖ ⟩
      ⇒ ComputationInBox k* AtTime m       ∴⟨ state-steps m≤e ⟩
      ⇒ StateIn (B k*) AtTime e            ∴⟨ (λ prf i → prf i (<-wellFounded e)) ⟩
      ⇒ asyncₜ e ∈ᵢ B k*                    ∴⟨ last-step ⟩ 
      ⇒ asyncₜ e ≈ x*                      ∎
      where
             last-step : asyncₜ e ∈ᵢ B k* → asyncₜ e ≈ x*
             last-step = proj₂ (proj₂ (proj₂ B-finish) ≤-refl)


convergent : ConvergesOver I∥ (B 0) 
convergent = record
  { x*         = x*
  ; k*         = k*
  ; x*-fixed   = x*-fixed
  ; x*-reached = x*-reached
  }
