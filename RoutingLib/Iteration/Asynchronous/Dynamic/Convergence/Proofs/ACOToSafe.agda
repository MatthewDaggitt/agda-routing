open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset) renaming (_∈_ to _∈ₛ_; _∉_ to _∉ₛ_)
open import Data.Fin.Dec using (_∈?_)
open import Data.Maybe using (just; nothing)
open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties hiding (_≟_)
open import Data.Product as Prod using (∃; proj₂; proj₁; _,_; _×_; uncurry′)
open import Function using (_∘_; _$_)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using (<-wellFounded)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; subst₂; cong; cong₂; refl; sym; trans)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred; _⊆_) renaming (_∈_ to _∈ᵤ_)

open import RoutingLib.Relation.Binary.Indexed.Homogeneous
open import RoutingLib.Relation.Unary.Indexed
open import RoutingLib.Relation.Unary.Properties
open import RoutingLib.Function
open import RoutingLib.Function.Reasoning

open import RoutingLib.Iteration.Asynchronous.Dynamic
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions using (ACO)
open import RoutingLib.Iteration.Asynchronous.Dynamic.Properties using (asyncIter-cong; asyncIter-inactive)
open import RoutingLib.Iteration.Asynchronous.Schedule
import RoutingLib.Iteration.Asynchronous.Schedule.Pseudoperiod as Pseudoperiod


module RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Proofs.ACOToSafe
  {a ℓ n p} (𝓘 : AsyncIterable a ℓ n) (aco : ACO 𝓘 p) where

open AsyncIterable 𝓘
open ACO aco

-- The final state
ξ : Epoch → Subset n → S
ξ e p = proj₁ (proj₂ (D-finish e p))

-- The final box number
bᶠ : Epoch → Subset n → ℕ
bᶠ e p = proj₁ (D-finish e p)

module _ {x₀ : S} (x₀∈B : x₀ ∈ B) (𝓢 : Schedule n) where

  open Schedule 𝓢
  open Pseudoperiod 𝓢


  -- Shorthand notation for boxes (using time as an index)
  Dₜ : 𝕋 → ℕ → IPred Sᵢ p
  Dₜ t = D (η t) (ρ t)

  Dₜ-cong : ∀ {t s} → η t ≡ η s → Dₜ t ≡ Dₜ s
  Dₜ-cong ηₜ≡ηₛ = cong₂ D ηₜ≡ηₛ (cong π ηₜ≡ηₛ)

  -- Shorthand notation with various implicit variables
  
  async : ∀ {t} → Acc _<_ t → S
  async = asyncIter' 𝓘 𝓢 x₀
  
  asyncₜ : ∀ t → {rec : Acc _<_ t} → S
  asyncₜ t {rec} = async rec

  view : ∀ t i → {accβ : ∀ j → Acc _<_ (β (suc t) i j)} → S
  view t i {accβ} j = async (accβ j) j

  Fₜ : 𝕋 → S → S
  Fₜ t = F (η t) (ρ t)

  -- Membership substitution for equal times
  
  ∈Dₜᵢ-resp-rec : ∀ {t b} (rec₁ rec₂ : Acc _<_ t) →
                  ∀ {i} → async rec₁ i ∈ᵤ Dₜ t b i → async rec₂ i ∈ᵤ Dₜ t b i
  ∈Dₜᵢ-resp-rec rec₁ rec₂ = D-cong (asyncIter-cong 𝓘 𝓢 x₀ rec₁ rec₂ refl _)

  ∈Dₜ-resp-rec : ∀ {t b} (rec₁ rec₂ : Acc _<_ t) →
                  async rec₁ ∈ Dₜ t b → async rec₂ ∈ Dₜ t b
  ∈Dₜ-resp-rec rec₁ rec₂ async∈ i = ∈Dₜᵢ-resp-rec rec₁ rec₂ (async∈ i)

  async∈-resp-Dₜᵢ : ∀ t {b s e} {rec : Acc _<_ t} → η s ≡ η e →
                    ∀ {i} → async rec i ∈ᵤ Dₜ s b i → async rec i ∈ᵤ Dₜ e b i
  async∈-resp-Dₜᵢ t {rec = rec} ηₛ≡ηₑ = subst (λ v → async rec _ ∈ᵤ v _ _) (Dₜ-cong ηₛ≡ηₑ)

  async∈-resp-Dₜ : ∀ t {b s e} {rec : Acc _<_ t} → η s ≡ η e →
                   async rec ∈ Dₜ s b → async rec ∈ Dₜ e b
  async∈-resp-Dₜ t ηₛ≡ηₑ ∈b i = async∈-resp-Dₜᵢ t ηₛ≡ηₑ (∈b i)
  
  -- The concept of being locally safe

  StateOfNode_InBox_AtTime_ : Fin n → ℕ → 𝕋 → Set p
  StateOfNode i InBox b AtTime t = (acc : Acc _<_ t) → async acc i ∈ᵤ Dₜ t b i

  StateInBox_AtTime_ : ℕ → 𝕋 → Set p
  StateInBox b AtTime t = ∀ i → StateOfNode i InBox b AtTime t

  MessagesOfNode_InBox_AtTime_ : Fin n → ℕ → 𝕋 → Set p
  MessagesOfNode i InBox b AtTime t = ∀ {j s} → IsSubEpoch [ t , suc s ] → i ∈ₛ ρ (suc s) →
                                      (acc : Acc _<_ (β (suc s) i j)) → async acc j ∈ᵤ Dₜ (suc s) b j

  MessagesInBox_AtTime_ : 𝕋 → ℕ → Set p
  MessagesInBox b AtTime t = ∀ i → MessagesOfNode i InBox b AtTime t

  -- The concept of being in the initial box
  StateOfNode_InBAtTime_ : Fin n → 𝕋 → Set p
  StateOfNode i InBAtTime t = (acc : Acc _<_ t) → async acc i ∈ᵤ B i

  StateInBAtTime_ : 𝕋 → Set p
  StateInBAtTime t = ∀ i → StateOfNode i InBAtTime t

  MessagesOfNode_InBAtTime_ : Fin n →  𝕋 → Set p
  MessagesOfNode i InBAtTime t = ∀ {j s} → IsSubEpoch [ t , suc s ] → i ∈ₛ ρ (suc s) →
                                 (acc : Acc _<_ (β (suc s) i j)) → async acc j ∈ᵤ B j

  MessagesInBAtTime_ : 𝕋 → Set p
  MessagesInBAtTime t = ∀ i → MessagesOfNode i InBAtTime t

  -- Concept of all messages being the current epoch
  MessagesInSameEpoch : 𝕋 → Set
  MessagesInSameEpoch s = ∀ {t} → s ≤ suc t → η s ≡ η (suc t) → ∀ {i} → i ∈ₛ ρ (suc t) → ∀ j → η (β (suc t) i j) ≡ η s
  
  ------------------------------------------------------------------------
  -- Actual proofs
  ------------------------------------------------------------------------
  -- Not participating

  i∉ρ⇒stateᵢ∈Bₜ : ∀ {i t b} → i ∉ₛ ρ t → StateOfNode i InBox b AtTime t
  i∉ρ⇒stateᵢ∈Bₜ i∉ρₜ recₜ rewrite asyncIter-inactive 𝓘 𝓢 x₀ recₜ i∉ρₜ = D-null i∉ρₜ

  ------------------------------------------------------------------------
  -- Base case: the asynchronous iteration is always in the initial box

  expiry⇒messages∈η : ∀ {s e} →
                      IsExpiryPeriod [ s , e ] →
                      MessagesInSameEpoch e
  expiry⇒messages∈η {s} {e} expiry {t} e≤1+t ηₑ≡η₁₊ₜ {i} i∈ρ₁₊ₜ j = trans (η-inRangeₑ (trans ηₛ≡ηₑ ηₑ≡η₁₊ₜ) ((expiryᵢ (∈ρ-subst (trans (sym ηₑ≡η₁₊ₜ) (sym ηₛ≡ηₑ)) i∈ρ₁₊ₜ) e≤1+t j) , β-decreasing i j (s≤s z≤n))) (sym ηₑ≡η₁₊ₜ)
    where open IsExpiryPeriod expiry
    
  messages∈η-extend : ∀ {s e} → IsSubEpoch [ s , e ] →
                      MessagesInSameEpoch s →
                      MessagesInSameEpoch e
  messages∈η-extend (mkₛₑ s≤e ηₛ≡ηₑ) m∈e e≤t ηₑ≡ηₜ i∈ρ₁₊ₜ j =
    trans (m∈e (≤-trans s≤e e≤t) (trans ηₛ≡ηₑ ηₑ≡ηₜ) i∈ρ₁₊ₜ j) ηₛ≡ηₑ
  
  ------------------------------------------------------------------------
  -- Base case: the asynchronous iteration is always in the initial box
  
  state∈B : ∀ t → StateInBAtTime t
  state∈B zero    i (acc rec) with i ∈? ρ 0
  ... | no  _ = B-null i
  ... | yes _ = x₀∈B i
  state∈B (suc t) i (acc rec) with i ∈? ρ (suc t) | i ∈? ρ t | i ∈? α (suc t)
  ... | no  _ | _     | _     = B-null i
  ... | yes _ | no  _ | _     = x₀∈B i
  ... | yes _ | yes _ | no  _ = state∈B t i (rec t ≤-refl)
  ... | yes _ | yes _ | yes _ = F-resp-B (λ j → state∈B (β (suc t) i j) j (rec (β (suc t) i j) _)) i

  messages∈B : ∀ t → MessagesInBAtTime t 
  messages∈B t i {j} {s} _ _ = state∈B (β (suc s) i j) j

  ------------------------------------------------------------------------
  -- Preservation: if the asynchronous iteration is in a box and
  -- information recieved is in that box then assuming the epoch is the
  -- same, it will still be in that box in the future.

  state-steps : ∀ {b s e} → IsSubEpoch [ s , e ] →
                MessagesInSameEpoch s →
                MessagesInBox b AtTime s →
                StateInBox (suc b) AtTime s →
                StateInBox (suc b) AtTime e
  state-steps {b} {s} {zero}  ep@(mkₛₑ z≤n   _)        m∈e m∈b s∈b = s∈b
  state-steps {b} {s} {suc e} ep@(mkₛₑ s≤1+e ηₛ≡η₁₊ₑ) m∈e m∈b s∈b i (acc rec) with <-cmp s (suc e)
  ... | tri≈ _ refl _      = s∈b i (acc rec)
  ... | tri> _ _ s>1+e     = contradiction s≤1+e (<⇒≱ s>1+e)
  ... | tri< (s≤s s≤e) _ _ with η-inRange ηₛ≡η₁₊ₑ (s≤e , n≤1+n _)
  ...   | ηₛ≡ηₑ , ηₑ≡η₁₊ₑ with i ∈? ρ (suc e) | i ∈? ρ e | i ∈? α (suc e)
  ...     | no  i∉ρ₁₊ₑ | _       | _     = D-null i∉ρ₁₊ₑ
  ...     | yes i∈ρ₁₊ₑ | no i∉ρₑ | _     = contradiction (∈ρ-subst (sym ηₑ≡η₁₊ₑ) i∈ρ₁₊ₑ) i∉ρₑ
  ...     | yes i∈ρ₁₊ₑ | yes _   | yes _ = F-mono-D test (λ j → m∈b i ep i∈ρ₁₊ₑ _) i
    where
    test : ∀ {j} → j ∉ₛ ρ (suc e) → asyncₜ (β (suc e) i j) j ≈ᵢ ⊥ j
    test {j} j∉ρ₁₊ₑ = ≈ᵢ-reflexive (asyncIter-inactive 𝓘 𝓢 x₀ (rec (β (suc e) i j) _) (subst (λ v → j ∉ₛ π v) (trans (sym ηₛ≡η₁₊ₑ) (sym (m∈e s≤1+e ηₛ≡η₁₊ₑ i∈ρ₁₊ₑ j))) j∉ρ₁₊ₑ))
    
  ...     | yes _      | yes _    | no  _ = begin⟨ state-steps (mkₛₑ s≤e ηₛ≡ηₑ) m∈e m∈b s∈b i (rec e ≤-refl) ⟩
    ⇒ asyncₜ e i ∈ᵤ Dₜ e       (suc b) i ∴⟨ ∈Dₜᵢ-resp-rec _ (rec e ≤-refl) ⟩
    ⇒ asyncₜ e i ∈ᵤ Dₜ e       (suc b) i ∴⟨ async∈-resp-Dₜᵢ e ηₑ≡η₁₊ₑ ⟩
    ⇒ asyncₜ e i ∈ᵤ Dₜ (suc e) (suc b) i ∎

  message-steps : ∀ {b s e} →
                  IsSubEpoch [ s , e ] → 
                  MessagesInBox b AtTime s →
                  MessagesInBox b AtTime e
  message-steps [s,e]-ep m∈b i [e,1+t]-ep = m∈b i ([s,e]-ep ++ₛₑ [e,1+t]-ep)

  state-steps-B : ∀ {s e} → IsSubEpoch [ s , e ] →
                MessagesInBAtTime s →
                StateInBox 0 AtTime s →
                StateInBox 0 AtTime e
  state-steps-B {s} {zero}  ep@(mkₛₑ z≤n   _)       m∈b s∈b = s∈b
  state-steps-B {s} {suc e} ep@(mkₛₑ s≤1+e ηₛ≡η₁₊ₑ) m∈b s∈b i (acc rec) with <-cmp s (suc e)
  ... | tri≈ _ refl _      = s∈b i (acc rec)
  ... | tri> _ _ s>1+e     = contradiction s≤1+e (<⇒≱ s>1+e)
  ... | tri< (s≤s s≤e) _ _ with η-inRange ηₛ≡η₁₊ₑ (s≤e , n≤1+n _)
  ...   | ηₛ≡ηₑ , ηₑ≡η₁₊ₑ with i ∈? ρ (suc e) | i ∈? ρ e | i ∈? α (suc e)
  ...     | no  i∉ρ₁₊ₑ | _       | _     = D-null i∉ρ₁₊ₑ
  ...     | yes i∈ρ₁₊ₑ | no i∉ρₑ | _     = contradiction (∈ρ-subst (sym ηₑ≡η₁₊ₑ) i∈ρ₁₊ₑ) i∉ρₑ
  ...     | yes i∈ρ₁₊ₑ | yes _   | yes _ = D-from-B (λ j → m∈b i ep i∈ρ₁₊ₑ _) i
  ...     | yes _      | yes _    | no  _ = begin⟨ state-steps-B (mkₛₑ s≤e ηₛ≡ηₑ) m∈b s∈b i (rec e ≤-refl) ⟩
    ⇒ asyncₜ e i ∈ᵤ Dₜ e       0 i ∴⟨ ∈Dₜᵢ-resp-rec _ (rec e ≤-refl) ⟩
    ⇒ asyncₜ e i ∈ᵤ Dₜ e       0 i ∴⟨ async∈-resp-Dₜᵢ e ηₑ≡η₁₊ₑ ⟩
    ⇒ asyncₜ e i ∈ᵤ Dₜ (suc e) 0 i ∎
    
  ------------------------------------------------------------------------
  -- Step: after one pseudoperiod the node is guaranteed to have
  -- advanced at least one box

  messages∈Dₖᵢ⇒state∈D₁₊ₖᵢ : ∀ {s e i b} →
                             i IsActiveIn [ s , e ] → 
                             MessagesInSameEpoch s →
                             MessagesOfNode i InBox b AtTime s →
                             StateOfNode i InBox (suc b) AtTime e
  messages∈Dₖᵢ⇒state∈D₁₊ₖᵢ {s} {zero}  {i} (mkₐ _       _ ()  z≤n   _)
  messages∈Dₖᵢ⇒state∈D₁₊ₖᵢ {s} {suc e} {i} (mkₐ ηₛ≡η₁₊ₑ m s<m m≤1+e i∈αₘ) m∈e m∈B (acc recₑ)
    with η-inRange ηₛ≡η₁₊ₑ (≤-pred (≤-trans s<m m≤1+e) , n≤1+n _)
  ... | ηₛ≡ηₑ , ηₑ≡η₁₊ₑ with i ∈? ρ (suc e) | i ∈? ρ e | i ∈? α (suc e)
  ...   | no  i∉ρ₁₊ₑ | _       | _     = D-null i∉ρ₁₊ₑ
  ...   | yes i∈ρ₁₊ₑ | no i∉ρₑ | _     = contradiction (∈ρ-subst (sym ηₑ≡η₁₊ₑ) i∈ρ₁₊ₑ) i∉ρₑ
  ...   | yes i∈ρ₁₊ₑ | yes _   | yes _ = F-mono-D (λ j∉p → ≈ᵢ-reflexive (asyncIter-inactive 𝓘 𝓢 x₀ (recₑ (β (suc e) i _) _) (j∉p ∘ subst (λ v → _ ∈ₛ π v) (trans (m∈e (≤-trans (<⇒≤ s<m) m≤1+e) ηₛ≡η₁₊ₑ i∈ρ₁₊ₑ _) ηₛ≡η₁₊ₑ)))) (λ j → m∈B (mkₛₑ s≤1+e ηₛ≡η₁₊ₑ) i∈ρ₁₊ₑ _) i
    where s≤1+e = ≤-trans (n≤1+n s) (≤-trans s<m m≤1+e)
  ...   | yes _       | yes _   | no  i∉α₁₊ₑ with m ≟ℕ suc e
  ...     | yes refl  = contradiction i∈αₘ i∉α₁₊ₑ
  ...     | no  m≢1+e = async∈-resp-Dₜᵢ e ηₑ≡η₁₊ₑ (messages∈Dₖᵢ⇒state∈D₁₊ₖᵢ (mkₐ ηₛ≡ηₑ m s<m m≤e i∈αₘ) m∈e m∈B _)
    where m≤e = ≤-pred (≤∧≢⇒< m≤1+e m≢1+e)

  messages∈Dₖ⇒state∈D₁₊ₖ : ∀ {s e b} →
                           IsActivationPeriod [ s , e ] →
                           MessagesInSameEpoch s →
                           MessagesInBox b AtTime s →
                           StateInBox (suc b) AtTime e
  messages∈Dₖ⇒state∈D₁₊ₖ {s} {e} active m∈e m∈b i with i ∈? ρ s 
  ... | no  i∉ρₛ = i∉ρ⇒stateᵢ∈Bₜ (i∉ρₛ ∘ ∈ρ-subst (sym (IsActivationPeriod.ηₛ≡ηₑ active)))
  ... | yes i∈ρₛ = messages∈Dₖᵢ⇒state∈D₁₊ₖᵢ (isActivation i∈ρₛ) m∈e (m∈b i) 
    where open IsActivationPeriod active

  messages-pp : ∀ {e s b} →
               IsPseudoperiodic [ s , e ] →
               MessagesInSameEpoch s →
               MessagesInBox b AtTime s →
               MessagesInBox (suc b) AtTime e
  messages-pp {e} {s} {b} pp m∈e m∈B i {j} {t} (mkₛₑ e≤1+t ηₑ≡η₁₊ₜ) i∈ρ₁₊ₜ accβ = begin⟨ test accβ ⟩
    ⇒ async accβ j ∈ᵤ Dₜ (β (suc t) i j) (suc b) j ∴⟨ async∈-resp-Dₜᵢ (β (suc t) i j) ηβ≡η₁₊ₜ ⟩
    ⇒ async accβ j ∈ᵤ Dₜ (suc t)         (suc b) j ∎
    where
    open IsPseudoperiodic pp
    
    ηₛ≡η₁₊ₜ : η s ≡ η (suc t)
    ηₛ≡η₁₊ₜ = trans ηₛ≡ηₑ ηₑ≡η₁₊ₜ
    
    i∈ρₛ : i ∈ₛ ρ s
    i∈ρₛ = ∈ρ-subst (sym ηₛ≡η₁₊ₜ) i∈ρ₁₊ₜ
    
    i∈ρₘ : i ∈ₛ ρ mid
    i∈ρₘ = ∈ρ-subst ηₛ≡ηₘ i∈ρₛ
    
    β∈[s,1+t] : β (suc t) i j ∈ₜ [ s , suc t ]
    β∈[s,1+t] = ≤-trans start≤mid (expiryᵢ i∈ρₘ e≤1+t j) , β-decreasing i j (s≤s z≤n)

    ηₛ≡ηβ : η s ≡ η (β (suc t) i j)
    ηₛ≡ηβ = η-inRangeₛ ηₛ≡η₁₊ₜ β∈[s,1+t]

    ηβ≡η₁₊ₜ : η (β (suc t) i j) ≡ η (suc t)
    ηβ≡η₁₊ₜ = η-inRangeₑ ηₛ≡η₁₊ₜ β∈[s,1+t]
    
    test : StateOfNode j InBox (suc b) AtTime (β (suc t) i j)
    test with j ∈? ρ s
    ... | no  j∉ρₛ = i∉ρ⇒stateᵢ∈Bₜ (j∉ρₛ ∘ subst (λ v → j ∈ₛ π v) (sym ηₛ≡ηβ))
    ... | yes j∈ρₛ = messages∈Dₖᵢ⇒state∈D₁₊ₖᵢ (mkₐ ηₛ≡ηβ (α+ j∈ρₛ) (s<α+ j∈ρₛ) (α+≤β i i∈ρₛ j∈ρₛ e≤1+t) (i∈α+[i] j∈ρₛ)) m∈e (m∈B j)


  ------------------------------------------------------------------------
  -- From B to D

  messages∈Bᵢ⇒state∈D₀ᵢ : ∀ {s e i} →
                          i IsActiveIn [ s , e ] → 
                          MessagesOfNode i InBAtTime s →
                          StateOfNode i InBox 0 AtTime e
  messages∈Bᵢ⇒state∈D₀ᵢ {s} {zero}  {i} (mkₐ _       _ ()  z≤n   _)
  messages∈Bᵢ⇒state∈D₀ᵢ {s} {suc e} {i} (mkₐ ηₛ≡η₁₊ₑ m s<m m≤1+e i∈αₘ)  m∈B (acc recₑ)
    with η-inRange ηₛ≡η₁₊ₑ (≤-pred (≤-trans s<m m≤1+e) , n≤1+n _)
  ... | ηₛ≡ηₑ , ηₑ≡η₁₊ₑ with i ∈? ρ (suc e) | i ∈? ρ e | i ∈? α (suc e)
  ...   | no  i∉ρ₁₊ₑ | _       | _     = D-null i∉ρ₁₊ₑ
  ...   | yes i∈ρ₁₊ₑ | no i∉ρₑ | _     = contradiction (∈ρ-subst (sym ηₑ≡η₁₊ₑ) i∈ρ₁₊ₑ) i∉ρₑ
  ...   | yes i∈ρ₁₊ₑ | yes _   | yes _ = D-from-B (λ j → m∈B (mkₛₑ s≤1+e ηₛ≡η₁₊ₑ) i∈ρ₁₊ₑ _) i
    where s≤1+e = ≤-trans (n≤1+n s) (≤-trans s<m m≤1+e)
  ...   | yes _       | yes _   | no  i∉α₁₊ₑ with m ≟ℕ suc e
  ...     | yes refl  = contradiction i∈αₘ i∉α₁₊ₑ
  ...     | no  m≢1+e = async∈-resp-Dₜᵢ e ηₑ≡η₁₊ₑ (messages∈Bᵢ⇒state∈D₀ᵢ (mkₐ ηₛ≡ηₑ m s<m m≤e i∈αₘ) m∈B _)
    where m≤e = ≤-pred (≤∧≢⇒< m≤1+e m≢1+e)

  messages∈B⇒state∈D₀ : ∀ {s e} →
                        IsActivationPeriod [ s , e ] →
                        MessagesInBAtTime s →
                        StateInBox 0 AtTime e
  messages∈B⇒state∈D₀ {s} {e} active m∈b i with i ∈? ρ s 
  ... | no  i∉ρₛ = i∉ρ⇒stateᵢ∈Bₜ (i∉ρₛ ∘ ∈ρ-subst (sym (IsActivationPeriod.ηₛ≡ηₑ active)))
  ... | yes i∈ρₛ = messages∈Bᵢ⇒state∈D₀ᵢ (isActivation i∈ρₛ) (m∈b i) 
    where open IsActivationPeriod active

  messages∈B-pp : ∀ {e s} →
               IsPseudoperiodic [ s , e ] →
               MessagesInBAtTime s →
               MessagesInBox 0 AtTime e
  messages∈B-pp {e} {s} pp m∈B i {j} {t} (mkₛₑ e≤1+t ηₑ≡η₁₊ₜ) i∈ρ₁₊ₜ accβ = begin⟨ test accβ ⟩
    ⇒ async accβ j ∈ᵤ Dₜ (β (suc t) i j) 0 j ∴⟨ async∈-resp-Dₜᵢ (β (suc t) i j) ηβ≡η₁₊ₜ ⟩
    ⇒ async accβ j ∈ᵤ Dₜ (suc t)         0 j ∎
    where
    open IsPseudoperiodic pp
    
    ηₛ≡η₁₊ₜ : η s ≡ η (suc t)
    ηₛ≡η₁₊ₜ = trans ηₛ≡ηₑ ηₑ≡η₁₊ₜ
    
    i∈ρₛ : i ∈ₛ ρ s
    i∈ρₛ = ∈ρ-subst (sym ηₛ≡η₁₊ₜ) i∈ρ₁₊ₜ
    
    i∈ρₘ : i ∈ₛ ρ mid
    i∈ρₘ = ∈ρ-subst ηₛ≡ηₘ i∈ρₛ
    
    β∈[s,1+t] : β (suc t) i j ∈ₜ [ s , suc t ]
    β∈[s,1+t] = ≤-trans start≤mid (expiryᵢ i∈ρₘ e≤1+t j) , β-decreasing i j (s≤s z≤n)

    ηₛ≡ηβ : η s ≡ η (β (suc t) i j)
    ηₛ≡ηβ = η-inRangeₛ ηₛ≡η₁₊ₜ β∈[s,1+t]

    ηβ≡η₁₊ₜ : η (β (suc t) i j) ≡ η (suc t)
    ηβ≡η₁₊ₜ = η-inRangeₑ ηₛ≡η₁₊ₜ β∈[s,1+t]
    
    test : StateOfNode j InBox 0 AtTime (β (suc t) i j)
    test with j ∈? ρ s
    ... | no  j∉ρₛ = i∉ρ⇒stateᵢ∈Bₜ (j∉ρₛ ∘ subst (λ v → j ∈ₛ π v) (sym ηₛ≡ηβ))
    ... | yes j∈ρₛ = messages∈Bᵢ⇒state∈D₀ᵢ (mkₐ ηₛ≡ηβ (α+ j∈ρₛ) (s<α+ j∈ρₛ) (α+≤β i i∈ρₛ j∈ρₛ e≤1+t) (i∈α+[i] j∈ρₛ)) (m∈B j)
    
  ------------------------------------------------------------------------
  -- Steps : after k pseudoperiods all nodes are guaranteed to have
  -- advanced at least k boxes

  messages-mpp : ∀ {s e k b} →
                 IsMultiPseudoperiodic k [ s , e ] →
                 MessagesInSameEpoch s →
                 MessagesInBox b       AtTime s →
                 MessagesInBox (k + b) AtTime e
  messages-mpp {_} {_} {_}     {b} none            m∈e m∈b = m∈b
  messages-mpp {s} {e} {suc k} {b} (next m pp mpp) m∈e m∈b = begin⟨ m∈b ⟩
    ⇒ MessagesInBox b           AtTime s ∴⟨ messages-pp pp m∈e ⟩
    ⇒ MessagesInBox (suc b)     AtTime m ∴⟨ messages-mpp mpp (messages∈η-extend (IsPseudoperiodic.[s,e]-isEpochal pp) m∈e) ⟩
    ⇒ MessagesInBox (k + suc b) AtTime e ∴⟨ subst (MessagesInBox_AtTime e) (+-suc k b) ⟩
    ⇒ MessagesInBox (suc k + b) AtTime e ∎
  
  ------------------------------------------------------------------------
  -- Convergence

  messages∈Dₖ : ∀ {s e k} →
                IsMultiPseudoperiodic (suc k) [ s , e ] →
                MessagesInSameEpoch s →
                MessagesInBox k AtTime e
  messages∈Dₖ {s} {e} {k} (next m pp mpp) m∈e = begin⟨ messages∈B s ⟩
    ⇒ MessagesInBAtTime            s ∴⟨ messages∈B-pp pp ⟩
    ⇒ MessagesInBox 0       AtTime m ∴⟨ messages-mpp mpp (messages∈η-extend (IsPseudoperiodic.[s,e]-isEpochal pp) m∈e) ⟩
    ⇒ MessagesInBox (k + 0) AtTime e ∴⟨ subst (MessagesInBox_AtTime e) (+-identityʳ k) ⟩
    ⇒ MessagesInBox (k)     AtTime e ∎

  messages∈Dₖ+ : ∀ {s e k} →
                 IsConvergentPeriod (suc (suc k)) [ s , e ] →
                 MessagesInBox k AtTime e
  messages∈Dₖ+ {s} {e} {k} cp = begin⟨ mpp ⟩
    ⇒ IsMultiPseudoperiodic (suc k) [ mid₁ , mid₂ ] ∴⟨ (λ prf → messages∈Dₖ prf (expiry⇒messages∈η expiry)) ⟩
    ⇒ MessagesInBox k AtTime mid₂                   ∴⟨ message-steps [m₂,e]-isEpochal ⟩
    ⇒ MessagesInBox k AtTime e                      ∎
    where open IsConvergentPeriod cp

  state∈Dₖ+ : ∀ {s e t k} →
              IsConvergentPeriod (suc k) [ s , e ] →
              IsSubEpoch [ e , t ] →
              StateInBox k AtTime t
  state∈Dₖ+  {s} {e} {t} {zero} cp ep = begin⟨ messages∈B mid₂ ⟩
    ⇒ MessagesInBAtTime mid₂ ∴⟨ messages∈B⇒state∈D₀ active ⟩
    ⇒ StateInBox 0 AtTime e  ∴⟨ state-steps-B ep (messages∈B e) ⟩
    ⇒ StateInBox 0 AtTime t  ∎
    where open IsConvergentPeriod cp
  state∈Dₖ+  {s} {e} {t} {suc k} cp ep = begin⟨ messages∈Dₖ mpp m∈e ⟩
    ⇒ MessagesInBox     k AtTime mid₂  ∴⟨ messages∈Dₖ⇒state∈D₁₊ₖ active (messages∈η-extend [m₁,m₂]-isEpochal m∈e) ⟩
    ⇒ StateInBox    suc k AtTime e     ∴⟨ state-steps ep (messages∈η-extend ([m₁,m₂]-isEpochal ++ₛₑ [m₂,e]-isEpochal) m∈e) (messages∈Dₖ+ cp) ⟩
    ⇒ StateInBox    suc k AtTime t     ∎
    where
    open IsConvergentPeriod cp
    m∈e : MessagesInSameEpoch mid₁
    m∈e = expiry⇒messages∈η expiry
    
  ξ-reached : ∀ {s} → ∃ λ k → ∀ {m e} →
              IsConvergentPeriod k [ s , m ] →
              IsSubEpoch [ m , e ] →
              async (<-wellFounded e) ≈ ξ (η s) (ρ s)
  ξ-reached {s} = suc k , λ {m} {e} cp ep → begin⟨ state∈Dₖ+ cp ep ⟩
    ⇒ StateInBox k AtTime e    ∴⟨ (λ prf i → prf i (<-wellFounded e)) ⟩
    ⇒ asyncₜ e ∈ Dₜ e k        ∴⟨ async∈-resp-Dₜ e (sym (trans (IsConvergentPeriod.ηₛ≡ηₑ cp) (IsSubEpoch.ηₛ≡ηₑ ep))) ⟩
    ⇒ asyncₜ e ∈ Dₜ s k        ∴⟨ proj₂ (proj₂ (D-finish (η s) (ρ s))) ⟩
    ⇒ asyncₜ e ≈ ξ (η s) (ρ s) ∎
    where k = bᶠ (η s) (ρ s)

isSafe : IsSafeOver 𝓘 B
isSafe = record
  { m*         = ξ
  ; m*-reached = ξ-reached
  }
