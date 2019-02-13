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

open import RoutingLib.Iteration.Asynchronous.Static
open import RoutingLib.Iteration.Asynchronous.Static.Convergence.Conditions

module RoutingLib.Iteration.Asynchronous.Static.Convergence.ACOImpliesConverges
  {a ℓ₁ ℓ₂ n}
  (I∥ : AsyncIterable a ℓ₁ n)
  (aco : ACO I∥ ℓ₂)
  where

open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; ⊤)
  renaming (_∈_ to _∈ₛ_; _∉_ to _∉ₛ_)
open import Data.Fin.Dec using (_∈?_)
open import Data.Maybe using (just; nothing)
open import Data.Nat renaming (_≟_ to _≟ℕ_) hiding (_⊔_)
open import Data.Nat.Properties hiding (_≟_)
open import Data.Product using (∃; proj₂; proj₁; _,_; _×_; map)
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

open import RoutingLib.Iteration.Asynchronous.Static.Schedule
import RoutingLib.Iteration.Asynchronous.Static.Schedule.Pseudoperiod
  as Pseudoperiods
import RoutingLib.Iteration.Asynchronous.Static.Convergence.Properties.ACO
  as ACOProperties

open AsyncIterable I∥
open ACO  aco
open ACOProperties I∥ aco

------------------------------------------------------------------------
-- Notation

module _ {x : S} (x∈B₀ : x ∈ᵢ B 0) (ψ : Schedule n) where

  open Schedule ψ
  open Pseudoperiods ψ

  -- Some shorthand notation where the epoch and participant indices are
  -- replaced with a time index.

  δ' : S → ∀ {t} → Acc _<_ t → S
  δ' = asyncIter' I∥ ψ
  
  δ : S → 𝕋 → S
  δ x t = δ' x (<-wellFounded t)


  -- The concept of being locally safe

  StateOfNode_InBox_AtTime_ : Fin n → ℕ → 𝕋 → Set ℓ₂
  StateOfNode i InBox k AtTime t = (tₐ : Acc _<_ t) → δ' x tₐ i ∈ B k i

  StateInBox_AtTime_ : ℕ → 𝕋 → Set ℓ₂
  StateInBox k AtTime t = ∀ i → StateOfNode i InBox k AtTime t

  MessagesToNode_InBox_AtTime_ : Fin n → ℕ → 𝕋 → Set ℓ₂
  MessagesToNode i InBox k AtTime t = ∀ {s} → t < s → ∀ {j} → (βₐ : Acc _<_ (β s i j)) → δ' x βₐ j ∈ B k j

  MessagesInBox_AtTime_ : ℕ → 𝕋 → Set ℓ₂
  MessagesInBox k AtTime t = ∀ i → MessagesToNode i InBox k AtTime t

  ComputationInBox_AtTime_ : ℕ → 𝕋 → Set ℓ₂
  ComputationInBox k AtTime t = MessagesInBox (k ∸ 1) AtTime t × StateInBox k AtTime t

--------------------------------------------------------------------------
-- Actual proofs
--------------------------------------------------------------------------
-- Base case: the asynchronous iteration is always in the initial box

  state∈B₀ : ∀ t → StateInBox 0 AtTime t
  state∈B₀ zero    i (acc rec) = x∈B₀ i
  state∈B₀ (suc t) i (acc rec) with i ∈? α (suc t)
  ... | no  _ = state∈B₀ t i (rec t _)
  ... | yes _ = F-resp-B₀ (λ j → state∈B₀ (β (suc t) i j) j _) i 

  messages∈B₀ : ∀ t → MessagesInBox 0 AtTime t
  messages∈B₀ t i {s} t<s {j} = state∈B₀ (β s i j) j

  computation∈B₀ : ∀ t → ComputationInBox 0 AtTime t
  computation∈B₀ t = messages∈B₀ t , state∈B₀ t
  
--------------------------------------------------------------------------
-- Preservation: if the asynchronous iteration is in a box, 
-- then it will still be in that box in the future.

  state-stability : ∀ {k s e} → s ≤ e →
                ComputationInBox k AtTime s →
                StateInBox k AtTime e
  state-stability {k}     {s} {zero}  z≤n   c∈Bₖ = proj₂ c∈Bₖ
  state-stability {zero}  {s} {suc e} s≤1+e c∈Bₖ = state∈B₀ (suc e)
  state-stability {suc k} {s} {suc e} s≤1+e c∈Bₖ i (acc rec) with <-cmp s (suc e)
  ... | tri≈ _ refl _      = proj₂ c∈Bₖ i (acc rec)
  ... | tri> _ _ s>1+e     = contradiction s≤1+e (<⇒≱ s>1+e)
  ... | tri< (s≤s s≤e) _ _ with i ∈? α (suc e)
  ...   | no  _ = state-stability s≤e c∈Bₖ i (rec e ≤-refl)
  ...   | yes _ = F-mono-B (λ j → proj₁ c∈Bₖ i (s≤s s≤e) _) i

  message-stability : ∀ {k s e} → s ≤ e →
                      MessagesInBox k AtTime s →
                      MessagesInBox k AtTime e
  message-stability s≤e m∈b i e<t = m∈b i (<-transʳ s≤e e<t)

--------------------------------------------------------------------------
-- Step: after one pseudoperiod the node is guaranteed to have
-- advanced at least one box

  advance-stateᵢ : ∀ {s e i k} →
                   i IsActiveIn [ s , e ] →
                   MessagesToNode i InBox k AtTime s →
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
  advance-state (mkₐ v activeᵢ) m∈Bₖ i
    = advance-stateᵢ (activeᵢ i) (m∈Bₖ i)

  advance-messages : ∀ {s e k} →
                     ExpiryPeriod [ s , e ] →
                     ComputationInBox k AtTime s →
                     MessagesInBox k AtTime e
  advance-messages (mkₑ _ expiryᵢ) c∈Bₖ i e<t {j}
    = state-stability (expiryᵢ i j e<t) c∈Bₖ j

  advance-computation₁ : ∀ {s e k} →
                         Pseudocycle [ s , e ] →
                         ComputationInBox k       AtTime s →
                         ComputationInBox (suc k) AtTime e
  advance-computation₁ pp c∈Bₖ = m∈Bₖᵉ , s∈B₁₊ₖ
    where
    open Pseudocycle pp
    m∈Bₖᵐ  = advance-messages β[s,m] c∈Bₖ
    m∈Bₖᵉ   = message-stability mid≤end m∈Bₖᵐ
    s∈B₁₊ₖ  = advance-state α[m,e] m∈Bₖᵐ
  
  advance-computationₙ : ∀ {s e k n} →
                         MultiPseudocycle n [ s , e ] →
                         ComputationInBox k       AtTime s →
                         ComputationInBox (k + n) AtTime e
  advance-computationₙ {_} {_} {k} {zero}  none            c∈Bₖ rewrite +-identityʳ k = c∈Bₖ
  advance-computationₙ {s} {e} {k} {suc n} (next m pp mpp) c∈Bₖ = begin⟨ c∈Bₖ ⟩
    ⇒ ComputationInBox k           AtTime s ∴⟨ advance-computation₁ pp ⟩
    ⇒ ComputationInBox (suc k)     AtTime m ∴⟨ advance-computationₙ mpp ⟩
    ⇒ ComputationInBox (suc k + n) AtTime e ∴⟨ subst (ComputationInBox_AtTime e) (sym (+-suc k n)) ⟩
    ⇒ ComputationInBox (k + suc n) AtTime e ∎

--------------------------------------------------------------------------
-- Convergence

  x*-reached : ∀ {s e : 𝕋} →
               MultiPseudocycle k* [ s , e ] →
               ∀ {t : 𝕋} → e ≤ t → 
               δ x t ≈ x*
  x*-reached {s} {e} mpp {t} e≤t = begin⟨ computation∈B₀ s ⟩
    ⇒ ComputationInBox 0  AtTime s ∴⟨ advance-computationₙ mpp ⟩
    ⇒ ComputationInBox k* AtTime e ∴⟨ state-stability e≤t ⟩
    ⇒ StateInBox k* AtTime t       ∴⟨ (λ prf i → prf i (<-wellFounded t)) ⟩
    ⇒ δ x t ∈ᵢ B k*                ∴⟨ x∈B[k*]⇒x≈x* ⟩
    ⇒ δ x t ≈ x*                   ∎

convergent : ConvergesOver I∥ (B 0) 
convergent = record
  { x*         = x*
  ; k*         = k*
  ; x*-fixed   = x*-fixed
  ; x*-reached = x*-reached
  }
