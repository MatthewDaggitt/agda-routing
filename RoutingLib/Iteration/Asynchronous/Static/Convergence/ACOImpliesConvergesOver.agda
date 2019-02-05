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
  as Pseudoperiods


module RoutingLib.Iteration.Asynchronous.Static.Convergence.ACOImpliesConvergesOver
  {a ℓ ℓ₃ n}
  (I∥ : AsyncIterable a ℓ n)
  (aco : ACO I∥ ℓ₃)
   where

open AsyncIterable I∥
open ACO  aco


k* : ℕ
k* = proj₁ (B-finish)

x* : S
x* = proj₁ (proj₂ B-finish)

x*∈B[k*] : x* ∈ᵢ B k* 
x*∈B[k*] = proj₁ (proj₂ (proj₂ B-finish) ≤-refl)

x∈B[k*]⇒x≈x* : ∀ {x} → x ∈ᵢ B k* → x ≈ x* 
x∈B[k*]⇒x≈x* = proj₂ (proj₂ (proj₂ B-finish) ≤-refl)

x*-fixed : F x* ≈ x*
x*-fixed = begin⟨ x*∈B[k*] ⟩
  ⇒ x*   ∈ᵢ B k*       ∴⟨ F-mono-B ⟩
  ⇒ F x* ∈ᵢ B (suc k*) ∴⟨ proj₂ (proj₂ (proj₂ B-finish) (n≤1+n k*)) ⟩
  ⇒ F x* ≈ x*          ∎

------------------------------------------------------------------------
-- Notation

module _ {x₀ : S} (x₀∈B₀ : x₀ ∈ᵢ B 0) (𝓢 : Schedule n) where

  open Schedule 𝓢
  open Pseudoperiods 𝓢

  -- Some shorthand notation where the epoch and participant indices are
  -- replaced with a time index.

  δ' : S → ∀ {t} → Acc _<_ t → S
  δ' = asyncIter' I∥ 𝓢

  δ : S → 𝕋 → S
  δ x₀ t = δ' x₀ (<-wellFounded t)


  -- The concept of being locally safe

  StateOfNode_InBox_AtTime_ : Fin n → ℕ → 𝕋 → Set ℓ₃
  StateOfNode i InBox k AtTime t = (acc : Acc _<_ t) → δ' x₀ acc i ∈ B k i

  StateInBox_AtTime_ : ℕ → 𝕋 → Set ℓ₃
  StateInBox k AtTime t = ∀ i → StateOfNode i InBox k AtTime t

  MessagesOfNode_InBox_AtTime_ : Fin n → ℕ → 𝕋 → Set ℓ₃
  MessagesOfNode i InBox k AtTime t = ∀ {j s} → t < s → (acc : Acc _<_ (β s i j)) → δ' x₀ acc j ∈ B k j

  MessagesInBox_AtTime_ : ℕ → 𝕋 → Set ℓ₃
  MessagesInBox k AtTime t = ∀ i → MessagesOfNode i InBox k AtTime t

  ComputationInBox_AtTime_ : ℕ → 𝕋 → Set ℓ₃
  ComputationInBox k AtTime t = MessagesInBox (k ∸ 1) AtTime t × StateInBox k AtTime t

--------------------------------------------------------------------------
-- Actual proofs
--------------------------------------------------------------------------
-- Base case: the asynchronous iteration is always in the initial box

  state∈B₀ : ∀ t → StateInBox 0 AtTime t
  state∈B₀ zero    i (acc rec) = x₀∈B₀ i
  state∈B₀ (suc t) i (acc rec) with i ∈? α (suc t)
  ... | no  _ = state∈B₀ t i (rec t _)
  ... | yes _ = F-resp-B₀ (λ j → state∈B₀ (β (suc t) i j) j _) i 

  messages∈B₀ : ∀ t → MessagesInBox 0 AtTime t
  messages∈B₀ t i {j} {s} t<s rec = state∈B₀ (β s i j) j rec

  computation∈B₀ : ∀ t → ComputationInBox 0 AtTime t
  computation∈B₀ t = messages∈B₀ t , state∈B₀ t
  
--------------------------------------------------------------------------
-- Preservation: if the asynchronous iteration is in a box, 
-- then it will still be in that box in the future.

  state-steps : ∀ {k s e} → s ≤ e →
                ComputationInBox k AtTime s →
                StateInBox k AtTime e
  state-steps {k}     {s} {zero}  z≤n   c∈Bₖ = proj₂ c∈Bₖ
  state-steps {zero}  {s} {suc e} s≤1+e c∈Bₖ i rec = state∈B₀ (suc e) i rec
  state-steps {suc k} {s} {suc e} s≤1+e c∈Bₖ i (acc rec) with <-cmp s (suc e)
  ... | tri≈ _ refl _      = proj₂ c∈Bₖ i (acc rec)
  ... | tri> _ _ s>1+e     = contradiction s≤1+e (<⇒≱ s>1+e)
  ... | tri< (s≤s s≤e) _ _ with i ∈? α (suc e)
  ...   | no  _ = state-steps s≤e c∈Bₖ i (rec e ≤-refl)
  ...   | yes _ = F-mono-B (λ j → proj₁ c∈Bₖ i (s≤s s≤e) _) i

  message-steps : ∀ {k s e} →
                  s ≤ e →
                  MessagesInBox k AtTime s →
                  MessagesInBox k AtTime e
  message-steps s≤e m∈b i e<t recβ = m∈b i (<-transʳ s≤e e<t) recβ

--------------------------------------------------------------------------
-- Step: after one pseudoperiod the node is guaranteed to have
-- advanced at least one box

  advance-stateᵢ : ∀ {s e i k} →
                   i IsActiveIn [ s , e ] →
                   MessagesOfNode i InBox k AtTime s →
                   StateOfNode i InBox (suc k) AtTime e
  advance-stateᵢ {s} {zero}  {i} (mkₐᵢ m ()  z≤n   i∈αₘ)
  advance-stateᵢ {s} {suc e} {i} (mkₐᵢ m s<m m≤1+e i∈αₘ) m∈Bₖ (acc recₑ)
    with i ∈? α (suc e)
  ...   | yes _ = F-mono-B (λ j → m∈Bₖ (≤-trans s<m m≤1+e) _) i
  ...   | no  i∉α₁₊ₑ with m ≟ℕ suc e
  ...     | yes refl  = contradiction i∈αₘ i∉α₁₊ₑ
  ...     | no  m≢1+e = advance-stateᵢ (mkₐᵢ m s<m m≤e i∈αₘ) m∈Bₖ _
    where m≤e = ≤-pred (≤∧≢⇒< m≤1+e m≢1+e)

  advance-state : ∀ {s e k} →
                  ActivationPeriod [ s , e ] →
                  MessagesInBox k AtTime s →
                  StateInBox (suc k) AtTime e
  advance-state {s} {e} {k} (mkₐ v activeᵢ) m∈Bₖ i
    = advance-stateᵢ (activeᵢ i) (m∈Bₖ i)

  advance-messages : ∀ {s e k} →
                     ExpiryPeriod [ s , e ] →
                     ComputationInBox k AtTime s →
                     MessagesInBox k AtTime e
  advance-messages {s} (mkₑ _ expiryᵢ) c∈Bₖ i {j} e<t recβ
    = state-steps (expiryᵢ i j e<t) c∈Bₖ j recβ

--------------------------------------------------------------------------
-- Steps : after k pseudoperiods all nodes are guaranteed to have
-- advanced at least k boxes

  messages-pp : ∀ {s e k} →
                Pseudoperiod [ s , e ] →
                ComputationInBox k       AtTime s →
                ComputationInBox (suc k) AtTime e
  messages-pp pp c∈Bₖ = m∈Bₖᵉ , s∈B₁₊ₖ
    where
    open Pseudoperiod pp
    m∈Bₖᵐ  = advance-messages β[s,m] c∈Bₖ
    m∈Bₖᵉ   = message-steps mid≤end m∈Bₖᵐ
    s∈B₁₊ₖ  = advance-state α[m,e] m∈Bₖᵐ
  
  messages-mpp : ∀ {s e k n} →
                 MultiPseudoperiod n [ s , e ] →
                 ComputationInBox k       AtTime s →
                 ComputationInBox (n + k) AtTime e
  messages-mpp {_} {_} {_} {zero}  none            c∈Bₖ = c∈Bₖ
  messages-mpp {s} {e} {k} {suc n} (next m pp mpp) c∈Bₖ = begin⟨ c∈Bₖ ⟩
    ⇒ ComputationInBox k           AtTime s ∴⟨ messages-pp pp ⟩
    ⇒ ComputationInBox (suc k)     AtTime m ∴⟨ messages-mpp mpp ⟩
    ⇒ ComputationInBox (n + suc k) AtTime e ∴⟨ subst (ComputationInBox_AtTime e) (+-suc n k) ⟩
    ⇒ ComputationInBox (suc n + k) AtTime e ∎

--------------------------------------------------------------------------
-- Convergence

  computation∈Bₖ : ∀ {s e k} →
                   MultiPseudoperiod k [ s , e ] →
                   ComputationInBox k AtTime e
  computation∈Bₖ {s} {e} {zero}  none = computation∈B₀ s
  computation∈Bₖ {s} {e} {suc k} (next m pp mpp) = begin⟨ computation∈B₀ s ⟩
    ⇒ ComputationInBox 0       AtTime s ∴⟨ messages-pp pp ⟩
    ⇒ ComputationInBox 1       AtTime m ∴⟨ messages-mpp mpp ⟩
    ⇒ ComputationInBox (k + 1) AtTime e ∴⟨ subst (ComputationInBox_AtTime e) (+-comm k 1) ⟩
    ⇒ ComputationInBox (1 + k) AtTime e ∎

  x*-reached : ∀ {s m e : 𝕋} →
               MultiPseudoperiod k* [ s , m ] →
               m ≤ e → 
               δ x₀ e ≈ x*
  x*-reached {s} {m} {e} mpp m≤e = begin⟨ mpp ⟩
    ⇒ MultiPseudoperiod k* [ s , m ]  ∴⟨ computation∈Bₖ ⟩
    ⇒ ComputationInBox k* AtTime m    ∴⟨ state-steps m≤e ⟩
    ⇒ StateInBox k* AtTime e          ∴⟨ (λ prf i → prf i (<-wellFounded e)) ⟩
    ⇒ δ x₀ e ∈ᵢ B k*                  ∴⟨ x∈B[k*]⇒x≈x* ⟩
    ⇒ δ x₀ e ≈ x*                     ∎

convergent : ConvergesOver I∥ (B 0) 
convergent = record
  { x*         = x*
  ; k*         = k*
  ; x*-fixed   = x*-fixed
  ; x*-reached = x*-reached
  }
