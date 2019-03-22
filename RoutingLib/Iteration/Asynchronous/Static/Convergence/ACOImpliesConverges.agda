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

open import RoutingLib.Relation.Unary.Indexed

open import RoutingLib.Iteration.Asynchronous.Static
open import RoutingLib.Iteration.Asynchronous.Static.Convergence.Conditions

module RoutingLib.Iteration.Asynchronous.Static.Convergence.ACOImpliesConverges
  {a ℓ₁ ℓ₂ ℓ₃ n}
  (I∥ : AsyncIterable a ℓ₁ n)
  {X₀ : IPred _ ℓ₂}
  (aco : PartialACO I∥ X₀ ℓ₃)
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
open import RoutingLib.Relation.Unary.Properties
open import RoutingLib.Function
open import RoutingLib.Function.Reasoning

open import RoutingLib.Iteration.Asynchronous.Static.Schedule
import RoutingLib.Iteration.Asynchronous.Static.Schedule.Pseudoperiod
  as Pseudoperiods
import RoutingLib.Iteration.Asynchronous.Static.Convergence.Properties.ACO
  as ACOProperties

open AsyncIterable I∥
open PartialACO  aco
open ACOProperties I∥ aco

------------------------------------------------------------------------
-- Notation

module _ {x : S} (x∈X₀ : x ∈ᵢ X₀) (ψ : Schedule n) where

  open Schedule ψ
  open Pseudoperiods ψ

  -- Some shorthand notation where the epoch and participant indices are
  -- replaced with a time index.

  δ' : S → ∀ {t} → Acc _<_ t → S
  δ' = asyncIter' I∥ ψ
  
  δ : S → 𝕋 → S
  δ x t = δ' x (<-wellFounded t)


  -- The concept of being locally safe

  StateOfNode_InBox_AtTime_ : Fin n → ℕ → 𝕋 → Set ℓ₃
  StateOfNode i InBox k AtTime t = (tₐ : Acc _<_ t) → δ' x tₐ i ∈ D k i

  StateInBox_AtTime_ : ℕ → 𝕋 → Set ℓ₃
  StateInBox k AtTime t = ∀ i → StateOfNode i InBox k AtTime t

  MessagesToNode_InBox_AtTime_ : Fin n → ℕ → 𝕋 → Set ℓ₃
  MessagesToNode i InBox k AtTime t = ∀ {s} → t < s → ∀ {j} → (βₐ : Acc _<_ (β s i j)) → δ' x βₐ j ∈ D k j

  MessagesInBox_AtTime_ : ℕ → 𝕋 → Set ℓ₃
  MessagesInBox k AtTime t = ∀ i → MessagesToNode i InBox k AtTime t

  ComputationInBox_AtTime_ : ℕ → 𝕋 → Set ℓ₃
  ComputationInBox k AtTime t = ∀ i → MessagesToNode i InBox (k ∸ 1) AtTime t
                                    × StateOfNode i InBox k AtTime t

--------------------------------------------------------------------------
-- Actual proofs
--------------------------------------------------------------------------
-- Base case: the asynchronous iteration is always in the initial box

  state∈D₀ : ∀ t → StateInBox 0 AtTime t
  state∈D₀ zero    i (acc rec) = proj₁ X₀≋D₀ (x∈X₀ i)
  state∈D₀ (suc t) i (acc rec) with i ∈? α (suc t)
  ... | no  _ = state∈D₀ t i (rec t _)
  ... | yes _ = F-resp-D₀ (λ j → state∈D₀ (β (suc t) i j) j _) i 

  messages∈D₀ : ∀ t → MessagesInBox 0 AtTime t
  messages∈D₀ t i {s} t<s {j} = state∈D₀ (β s i j) j

  computation∈D₀ : ∀ t → ComputationInBox 0 AtTime t
  computation∈D₀ t i = messages∈D₀ t i , state∈D₀ t i
  
--------------------------------------------------------------------------
-- Preservation: if the asynchronous iteration is in a box, 
-- then it will still be in that box in the future.

  state-stability : ∀ {k s e i} → s ≤ e →
                    MessagesToNode i InBox (k ∸ 1) AtTime s ×
                    StateOfNode i InBox k AtTime s →
                    StateOfNode i InBox k AtTime e
  state-stability {k}     {s} {zero}  {i} z≤n   (_ , s∈Dₖ) = s∈Dₖ
  state-stability {zero}  {s} {suc e} {i} s≤1+e (_ , _) = state∈D₀ (suc e) i
  state-stability {suc k} {s} {suc e} {i} s≤1+e (m∈Dₖ , s∈D₁₊ₖ) (acc rec) with <-cmp s (suc e)
  ... | tri≈ _ refl _      = s∈D₁₊ₖ (acc rec)
  ... | tri> _ _ s>1+e     = contradiction s≤1+e (<⇒≱ s>1+e)
  ... | tri< (s≤s s≤e) _ _ with i ∈? α (suc e)
  ...   | no  _ = state-stability s≤e (m∈Dₖ , s∈D₁₊ₖ) (rec e ≤-refl)
  ...   | yes _ = F-mono-D (λ j → m∈Dₖ (s≤s s≤e) _) i

  message-stability : ∀ {k s e i} → s ≤ e →
                      MessagesToNode i InBox k AtTime s →
                      MessagesToNode i InBox k AtTime e
  message-stability s≤e m∈b e<t = m∈b (<-transʳ s≤e e<t)

  computation-stability : ∀ {k s e} → s ≤ e →
                          ComputationInBox k AtTime s →
                          ComputationInBox k AtTime e
  computation-stability s≤e c∈Dₖ i =
    message-stability s≤e (proj₁ (c∈Dₖ i)) , state-stability s≤e (c∈Dₖ i)

--------------------------------------------------------------------------
-- Step: after one pseudoperiod the node is guaranteed to have
-- advanced at least one box

  advance-state : ∀ {s e i k} →
                   i IsActiveIn [ s , e ] →
                   MessagesToNode i InBox k AtTime s →
                   StateOfNode i InBox (suc k) AtTime e
  advance-state {s} {zero}  {i} (mkₐ m ()  z≤n   i∈αₘ)
  advance-state {s} {suc e} {i} (mkₐ m s<m m≤1+e i∈αₘ) m∈Dₖ (acc recₑ)
    with i ∈? α (suc e)
  ...   | yes _ = F-mono-D (λ j → m∈Dₖ (≤-trans s<m m≤1+e) _) i
  ...   | no  i∉α₁₊ₑ with m ≟ℕ suc e
  ...     | yes refl  = contradiction i∈αₘ i∉α₁₊ₑ
  ...     | no  m≢1+e = advance-state (mkₐ m s<m m≤e i∈αₘ) m∈Dₖ _
    where m≤e = ≤-pred (≤∧≢⇒< m≤1+e m≢1+e)

  advance-messages : ∀ {s e k i} →
                     MessagesTo i ExpireIn [ s , e ] →
                     ComputationInBox k AtTime s →
                     MessagesToNode i InBox k AtTime e
  advance-messages (mkₑ _ expiryᵢ) c∈Dₖ e<t {j} =
    state-stability (expiryᵢ j e<t) (c∈Dₖ j)

  advance-computation₁ : ∀ {s e k} →
                         Pseudocycle [ s , e ] →
                         ComputationInBox k       AtTime s →
                         ComputationInBox (suc k) AtTime e
  advance-computation₁ pp c∈Dₖ i = messagesᵉ∈Dₖ , stateᵉ∈Dₖ₊₁ 
    where
    open Pseudocycle pp
    messagesᵐ∈Dₖ  = advance-messages (β[s,m] i) c∈Dₖ
    messagesᵉ∈Dₖ  = message-stability (midᵢ≤end i) messagesᵐ∈Dₖ
    stateᵉ∈Dₖ₊₁   = advance-state (α[m,e] i) messagesᵐ∈Dₖ

  advance-computationₙ : ∀ {s e k n} →
                         MultiPseudocycle n [ s , e ] →
                         ComputationInBox k       AtTime s →
                         ComputationInBox (k + n) AtTime e
  advance-computationₙ {_} {_} {k} {zero}  none            c∈Dₖ rewrite +-identityʳ k = c∈Dₖ
  advance-computationₙ {s} {e} {k} {suc n} (next m pp mpp) c∈Dₖ = begin⟨ c∈Dₖ ⟩
    ∴ ComputationInBox k           AtTime s $⟨ advance-computation₁ pp ⟩
    ∴ ComputationInBox (suc k)     AtTime m $⟨ advance-computationₙ mpp ⟩
    ∴ ComputationInBox (suc k + n) AtTime e $⟨ subst (ComputationInBox_AtTime e) (sym (+-suc k n)) ⟩
    ∴ ComputationInBox (k + suc n) AtTime e ∎

--------------------------------------------------------------------------
-- Convergence

  x*-reached : ∀ {s e : 𝕋} →
               MultiPseudocycle k* [ s , e ] →
               ∀ {t : 𝕋} → e ≤ t → 
               δ x t ≈ x*
  x*-reached {s} {e} mpp {t} e≤t = begin⟨ computation∈D₀ s ⟩
    ∴ ComputationInBox 0  AtTime s $⟨ advance-computationₙ mpp ⟩
    ∴ ComputationInBox k* AtTime e $⟨ state-stability e≤t ∘_ ⟩
    ∴ StateInBox k* AtTime t       $⟨ (λ prf i → prf i (<-wellFounded t)) ⟩
    ∴ δ x t ∈ᵢ D k*                $⟨ x∈D[k*]⇒x≈x* ⟩
    ∴ δ x t ≈ x*                   ∎

convergent : PartiallyConverges I∥ X₀ 
convergent = record
  { x*         = x*
  ; k*         = k*
  ; x*-fixed   = x*-fixed
  ; x*-reached = x*-reached
  }
