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
k* : Epoch → Subset n → ℕ
k* e p = proj₁ (D-finish e p)

D₀ : IPred Sᵢ p
D₀ = D 0 ⊤ 0

D₀-eqᵢ : ∀ {e p} f q i {x} → x ∈ᵤ D e p 0 i → x ∈ᵤ D f q 0 i
D₀-eqᵢ f q i x∈D₀ᵢ = D₀-eq f q {!!} i

module _ {x₀ : S} (x₀∈B : x₀ ∈ D₀) (𝓢 : Schedule n) where

  open Schedule 𝓢
  open Pseudoperiod 𝓢

  -- Some shorthand notation where the epoch and participant indices are
  -- replaced with a time index.

  Fₜ : 𝕋 → S → S
  Fₜ t = F (η t) (ρ t)
  
  Dₜ : 𝕋 → ℕ → IPred Sᵢ p
  Dₜ t = D (η t) (ρ t)

  async : ∀ {t} → Acc _<_ t → S
  async = asyncIter' 𝓘 𝓢 x₀
  
  asyncₜ : ∀ t → {rec : Acc _<_ t} → S
  asyncₜ t {rec} = async rec


  -- Membership substitution for equal times
  
  ∈Dₜᵢ-resp-rec : ∀ {t b} (rec₁ rec₂ : Acc _<_ t) →
                  ∀ {i} → async rec₁ i ∈ᵤ Dₜ t b i → async rec₂ i ∈ᵤ Dₜ t b i
  ∈Dₜᵢ-resp-rec rec₁ rec₂ = D-cong (asyncIter-cong 𝓘 𝓢 x₀ rec₁ rec₂ refl _)

  async∈-resp-Dₜᵢ : ∀ t {s e k} {rec : Acc _<_ t} → η s ≡ η e →
                    ∀ {i} → async rec i ∈ᵤ Dₜ s k i → async rec i ∈ᵤ Dₜ e k i
  async∈-resp-Dₜᵢ t {rec = rec} ηₛ≡ηₑ rewrite ηₛ≡ηₑ = id

  async∈-resp-Dₜ : ∀ t {b s e} {rec : Acc _<_ t} → η s ≡ η e →
                   async rec ∈ Dₜ s b → async rec ∈ Dₜ e b
  async∈-resp-Dₜ t ηₛ≡ηₑ ∈b i = async∈-resp-Dₜᵢ t ηₛ≡ηₑ (∈b i)
  
  -- The concept of being locally safe
  
  StateOfNode_In_AtTime_ : Fin n → IPred Sᵢ p → 𝕋 → Set p
  StateOfNode i In b AtTime t = (acc : Acc _<_ t) → async acc i ∈ᵤ b i

  StateIn_AtTime_ : IPred Sᵢ p → 𝕋 → Set p
  StateIn b AtTime t = ∀ i → StateOfNode i In b AtTime t

  MessagesOfNode_In_AtTime_ : Fin n → IPred Sᵢ p → 𝕋 → Set p
  MessagesOfNode i In b AtTime t = ∀ {j s} → IsSubEpoch [ t , suc s ] → i ∈ₛ ρ (suc s) →
                                   (acc : Acc _<_ (β (suc s) i j)) → async acc j ∈ᵤ b j

  MessagesIn_AtTime_ : IPred Sᵢ p → 𝕋 → Set p
  MessagesIn b AtTime t = ∀ i → MessagesOfNode i In b AtTime t


  -- Concept of all messages being the current epoch
  MessagesWellFormedAt : 𝕋 → Set ℓ
  MessagesWellFormedAt s = ∀ {i e} → IsSubEpoch [ s , suc e ] →
                           ∀ {j} {accβ : Acc _<_ (β (suc e) i j)} → i ∈ₛ ρ (suc e) → j ∉ₛ ρ (suc e) → async accβ j ≈ᵢ ⊥ j
  
  data ComputationInBox_AtTime_ : ℕ → 𝕋 → Set (p ⊔ ℓ) where
    zeroᵇ : ∀ {t} → MessagesWellFormedAt t →
            StateIn (Dₜ t 0) AtTime t →
            ComputationInBox 0 AtTime t
    sucᵇ  : ∀ {t k} → MessagesWellFormedAt t →
            MessagesIn (Dₜ t k) AtTime t →
            StateIn (Dₜ t (suc k)) AtTime t →
            ComputationInBox (suc k) AtTime t

  
  c∈Bₖ⇒s∈Bₖ : ∀ {t k} → ComputationInBox k AtTime t → StateIn (Dₜ t k) AtTime t
  c∈Bₖ⇒s∈Bₖ (zeroᵇ _ s∈Bₖ)   = s∈Bₖ
  c∈Bₖ⇒s∈Bₖ (sucᵇ  _ _ s∈Bₖ) = s∈Bₖ

  c∈Bₖ⇒m∈wf : ∀ {t k} → ComputationInBox k AtTime t → MessagesWellFormedAt t
  c∈Bₖ⇒m∈wf (zeroᵇ m∈wf _)   = m∈wf
  c∈Bₖ⇒m∈wf (sucᵇ  m∈wf _ _) = m∈wf
  
  ------------------------------------------------------------------------
  -- Actual proofs
  ------------------------------------------------------------------------
  -- Not participating

  i∉ρ⇒sᵢ∈Bₖᵢ : ∀ {i t k} → i ∉ₛ ρ t → StateOfNode i In (Dₜ t k) AtTime t
  i∉ρ⇒sᵢ∈Bₖᵢ {i} {t} {k} i∉ρₜ recₑ = begin⟨ D-null i∉ρₜ ⟩
    ⇒ ⊥ i        ∈ᵤ Dₜ t k i ∴⟨ D-cong (≈ᵢ-sym (≈ᵢ-reflexive (asyncIter-inactive 𝓘 𝓢 x₀ recₑ i∉ρₜ))) ⟩
    ⇒ asyncₜ t i ∈ᵤ Dₜ t k i ∎

  ------------------------------------------------------------------------
  -- Base case: the asynchronous iteration is always in the initial box
  
  state∈D₀ : ∀ t → StateIn (Dₜ t 0) AtTime t
  state∈D₀ zero    i (acc rec) with i ∈? ρ 0
  ... | no  i∉ρ₀ = D-null i∉ρ₀
  ... | yes _    = D₀-eq (η 0) (ρ 0) x₀∈B i
  state∈D₀ (suc t) i (acc rec) with i ∈? ρ (suc t) | i ∈? ρ t | i ∈? α (suc t)
  ... | no  i∉ρ₁₊ₜ | _     | _     = D-null i∉ρ₁₊ₜ
  ... | yes _       | no  _ | _     = D₀-eq (η (suc t)) (ρ (suc t)) x₀∈B i
  ... | yes _       | yes _ | no  _ = D₀-eq (η (suc t)) (ρ (suc t)) (λ j → state∈D₀ t j (rec t _)) i 
  ... | yes _       | yes _ | yes _ = F-resp-D₀ {η (suc t)} {ρ (suc t)} {λ j → async (rec (β (suc t) i j) _) j} (test) i
    where
    test : ∀ j → async (rec (β (suc t) i j) _) j ∈ᵤ Dₜ (suc t) 0 j
    test j = D₀-eq {η (β (suc t) i j)} {ρ (β (suc t) i j)} (η (suc t)) (ρ (suc t)) {!!} j
      where
      test2 : async (rec (β (suc t) i j) _) j ∈ᵤ Dₜ (β (suc t) i j) 0 j
      test2 = {!!}
      
    -- D₀-eq {η (β (suc t) i j)} {ρ (β (suc t) i j)} (η (suc t)) (ρ (suc t)) ? ?
--(D₀-eq (η (suc t)) (ρ (suc t)) (λ j → state∈D₀ (β (suc t) i j) j (rec _ _))) i
  
  expiry⇒wellFormed : ∀ {s e} →
                      IsExpiryPeriod [ s , e ] →
                      MessagesWellFormedAt e
  expiry⇒wellFormed {s} {e} (mkₑ (mkₛₑ s≤e ηₛ≡ηₑ) expiryᵢ) {i} {t} (mkₛₑ e≤1+t ηₑ≡η₁₊ₜ) {j} {accβ} i∈ρ₁₊ₑ j∉ρ₁₊ₜ =
    ≈ᵢ-reflexive (asyncIter-inactive 𝓘 𝓢 x₀ accβ (j∉ρ₁₊ₜ ∘ ∈ρ-subst (η-inRangeₑ (trans ηₛ≡ηₑ ηₑ≡η₁₊ₜ) (expiryᵢ (∈ρ-subst (sym (trans ηₛ≡ηₑ ηₑ≡η₁₊ₜ)) i∈ρ₁₊ₑ) e≤1+t j , β-decreasing i j (s≤s z≤n)))))

  ------------------------------------------------------------------------
  -- Preservation: if the asynchronous iteration is in a box and
  -- information recieved is in that box then assuming the epoch is the
  -- same, it will still be in that box in the future.

  wellFormed-steps : ∀ {s e} →
                     IsSubEpoch [ s , e ] →
                     MessagesWellFormedAt s →
                     MessagesWellFormedAt e
  wellFormed-steps η[s,e] wf η[s,1+t] = wf (η[s,e] ++ₛₑ η[s,1+t])
  
  state-steps : ∀ {k s e} →
                IsSubEpoch [ s , e ] →
                ComputationInBox k AtTime s →
                StateIn (Dₜ e k) AtTime e
  state-steps {k} {s} {zero}  η[s,e]@(mkₛₑ z≤n   _)        c∈Bₖ = c∈Bₖ⇒s∈Bₖ c∈Bₖ
  state-steps {k} {s} {suc e} η[s,e]@(mkₛₑ s≤1+e ηₛ≡η₁₊ₑ) c∈Bₖ i (acc rec) with <-cmp s (suc e)
  ... | tri≈ _ refl _      = c∈Bₖ⇒s∈Bₖ c∈Bₖ i (acc rec)
  ... | tri> _ _ s>1+e     = contradiction s≤1+e (<⇒≱ s>1+e)
  ... | tri< (s≤s s≤e) _ _ with η-inRange ηₛ≡η₁₊ₑ (s≤e , n≤1+n _)
  ...   | ηₛ≡ηₑ , ηₑ≡η₁₊ₑ with i ∈? ρ (suc e) | i ∈? ρ e | i ∈? α (suc e)
  ...     | no  i∉ρ₁₊ₑ | _       | _     = D-null i∉ρ₁₊ₑ
  ...     | yes i∈ρ₁₊ₑ | no i∉ρₑ | _     = contradiction (∈ρ-subst (sym ηₑ≡η₁₊ₑ) i∈ρ₁₊ₑ) i∉ρₑ
  ...     | yes _      | yes _   | no  _ = begin⟨ rec e ≤-refl ⟩
    ⇒ Acc _<_ e                    ∴⟨ state-steps (mkₛₑ s≤e ηₛ≡ηₑ) c∈Bₖ i  ⟩
    ⇒ asyncₜ e i ∈ᵤ Dₜ e       k i ∴⟨ ∈Dₜᵢ-resp-rec _ (rec e ≤-refl) ⟩
    ⇒ asyncₜ e i ∈ᵤ Dₜ e       k i ∴⟨ async∈-resp-Dₜᵢ e ηₑ≡η₁₊ₑ ⟩
    ⇒ asyncₜ e i ∈ᵤ Dₜ (suc e) k i ∎
  ...     | yes i∈ρ₁₊ₑ | yes _   | yes _ with c∈Bₖ
  ...       | zeroᵇ wf s∈D₀   = {!!} --F-mono-B (wf η[s,e] i∈ρ₁₊ₑ) (λ j → state∈D₀ (β (suc e) i j) j _) i
  ...       | sucᵇ  wf m∈Bₖ _ = F-mono-D (wf η[s,e] i∈ρ₁₊ₑ) (λ j → async∈-resp-Dₜᵢ (β (suc e) i j) ηₛ≡η₁₊ₑ (m∈Bₖ i η[s,e] i∈ρ₁₊ₑ _)) i
  
  message-steps : ∀ {k s e} →
                  IsSubEpoch [ s , e ] → 
                  MessagesIn (Dₜ s k) AtTime s →
                  MessagesIn (Dₜ e k) AtTime e
  message-steps η[s,e]@(mkₛₑ _ ηₛ≡ηₑ) m∈b i η[e,1+t] i∈ρ₁₊ₜ recβ =
    async∈-resp-Dₜᵢ (β _ _ _) ηₛ≡ηₑ (m∈b i (η[s,e] ++ₛₑ η[e,1+t]) i∈ρ₁₊ₜ recβ)

  ------------------------------------------------------------------------
  -- Step: after one pseudoperiod the node is guaranteed to have
  -- advanced at least one box
  -- (Dₜ s k)
  
  advance-stateᵢ : ∀ {s e i k} →
                   MessagesWellFormedAt s →
                   i IsActiveIn [ s , e ] → 
                   MessagesOfNode i In (Dₜ s k) AtTime s →
                   StateOfNode i In (Dₜ e (suc k)) AtTime e
  advance-stateᵢ {s} {zero}  {i} wf (mkₐᵢ ηₛ≡η₁₊ₑ m ()  z≤n   i∈αₘ)
  advance-stateᵢ {s} {suc e} {i} wf (mkₐᵢ ηₛ≡η₁₊ₑ m s<m m≤1+e i∈αₘ) m∈Bₖ (acc recₑ)
    with η-inRange ηₛ≡η₁₊ₑ (≤-pred (≤-trans s<m m≤1+e) , n≤1+n _)
  ... | ηₛ≡ηₑ , ηₑ≡η₁₊ₑ with i ∈? ρ (suc e) | i ∈? ρ e | i ∈? α (suc e)
  ...   | no  i∉ρ₁₊ₑ | _       | _     = D-null i∉ρ₁₊ₑ
  ...   | yes i∈ρ₁₊ₑ | no i∉ρₑ | _     = contradiction (∈ρ-subst (sym ηₑ≡η₁₊ₑ) i∈ρ₁₊ₑ) i∉ρₑ
  ...   | yes i∈ρ₁₊ₑ | yes _   | yes _ = F-mono-D (wf (mkₛₑ s≤1+e ηₛ≡η₁₊ₑ) i∈ρ₁₊ₑ) (λ j → async∈-resp-Dₜᵢ (β (suc e) i j) ηₛ≡η₁₊ₑ (m∈Bₖ (mkₛₑ s≤1+e ηₛ≡η₁₊ₑ) i∈ρ₁₊ₑ _)) i
    where s≤1+e = ≤-trans (n≤1+n s) (≤-trans s<m m≤1+e)
  ...   | yes _       | yes _   | no  i∉α₁₊ₑ with m ≟ℕ suc e
  ...     | yes refl  = contradiction i∈αₘ i∉α₁₊ₑ
  ...     | no  m≢1+e = async∈-resp-Dₜᵢ e ηₑ≡η₁₊ₑ (advance-stateᵢ wf (mkₐᵢ ηₛ≡ηₑ m s<m m≤e i∈αₘ) m∈Bₖ _)
    where m≤e = ≤-pred (≤∧≢⇒< m≤1+e m≢1+e)

  advance-state : ∀ {s e k} →
                  MessagesWellFormedAt s →
                  IsActivationPeriod [ s , e ] →
                  MessagesIn (Dₜ s k) AtTime s →
                  StateIn (Dₜ e (suc k)) AtTime e
  advance-state {s} {e} {k} wf (mkₐ (mkₛₑ _ ηₛ≡ηₑ) activeᵢ) m∈Bₖ i with i ∈? ρ s
  ... | no  i∉ρₛ = i∉ρ⇒sᵢ∈Bₖᵢ (i∉ρₛ ∘ ∈ρ-subst (sym ηₛ≡ηₑ))
  ... | yes i∈ρₛ = advance-stateᵢ wf (activeᵢ i∈ρₛ) (m∈Bₖ i)
    
  advance-messages : ∀ {s e k} →
                     IsExpiryPeriod [ s , e ] →
                     ComputationInBox k AtTime s →
                     MessagesIn (Dₜ e k) AtTime e
  advance-messages (mkₑ (mkₛₑ _ ηₛ≡ηₑ) expiryᵢ) c∈Bₖ i {j} (mkₛₑ e≤1+t ηₑ≡η₁₊ₜ) i∈ρ₁₊ₜ recβ
    with trans ηₛ≡ηₑ ηₑ≡η₁₊ₜ
  ... | ηₛ≡η₁₊ₜ with expiryᵢ (∈ρ-subst (sym ηₛ≡η₁₊ₜ) i∈ρ₁₊ₜ) e≤1+t j
  ...   | s≤β with η-inRange ηₛ≡η₁₊ₜ (s≤β , (β-decreasing i j (s≤s z≤n)))
  ...     | (ηₛ≡ηβ , ηβ≡η₁₊ₜ) = async∈-resp-Dₜᵢ (β _ _ _) (trans ηβ≡η₁₊ₜ (sym ηₑ≡η₁₊ₜ)) (state-steps (mkₛₑ s≤β ηₛ≡ηβ) c∈Bₖ j recβ)
  
  ------------------------------------------------------------------------
  -- Steps : after k pseudoperiods all nodes are guaranteed to have
  -- advanced at least k boxes

  start-pp : ∀ {s e} →
             IsPseudoperiodic [ s , e ] →
             ComputationInBox 0 AtTime e
  start-pp {s} {e} pp = zeroᵇ m∈wfᵉ s∈D₀
    where
    open IsPseudoperiodic pp
    m∈wfᵐ = expiry⇒wellFormed β[s,m]
    m∈wfᵉ = wellFormed-steps η[m,e] m∈wfᵐ
    s∈D₀  = state∈D₀ e

  messages-pp : ∀ {s e k} →
                IsPseudoperiodic [ s , e ] →
                ComputationInBox k       AtTime s →
                ComputationInBox (suc k) AtTime e
  messages-pp pp c∈Bₖ = sucᵇ m∈wfᵉ m∈Bₖᵉ s∈B₁₊ₖ
    where
    open IsPseudoperiodic pp
    m∈wfᵐ = wellFormed-steps η[s,m] (c∈Bₖ⇒m∈wf c∈Bₖ)
    m∈wfᵉ  = wellFormed-steps η[m,e] m∈wfᵐ
    m∈Bₖᵐ  = advance-messages β[s,m] c∈Bₖ
    m∈Bₖᵉ  = message-steps η[m,e] m∈Bₖᵐ
    s∈B₁₊ₖ = advance-state m∈wfᵐ α[m,e] m∈Bₖᵐ

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

  ------------------------------------------------------------------------
  -- Convergence

  computation∈Bₖ : ∀ {s e k} →
                   IsMultiPseudoperiodic (suc k) [ s , e ] →
                   ComputationInBox k AtTime e
  computation∈Bₖ {s} {e} {k} (next m pp mpp) = begin⟨ pp ⟩
    ⇒ IsPseudoperiodic [ s , m ]        ∴⟨ start-pp ⟩
    ⇒ ComputationInBox 0       AtTime m ∴⟨ messages-mpp mpp ⟩
    ⇒ ComputationInBox (k + 0) AtTime e ∴⟨ subst (ComputationInBox_AtTime e) (+-identityʳ k) ⟩
    ⇒ ComputationInBox k       AtTime e ∎

  ξ-reached′ : ∀ {s m e} →
               IsMultiPseudoperiodic (suc (k* (η s) (ρ s))) [ s , m ] →
               IsSubEpoch [ m , e ] →
               async (<-wellFounded e) ≈ ξ (η s) (ρ s)
  ξ-reached′ {s} {m} {e} mpp η[m,e]@(mkₛₑ m≤e ηₘ≡ηₑ) = begin⟨ mpp ⟩
    ⇒ IsMultiPseudoperiodic _ [ s , m ] ∴⟨ computation∈Bₖ ⟩
    ⇒ ComputationInBox k*' AtTime m     ∴⟨ state-steps η[m,e] ⟩
    ⇒ StateIn (Dₜ e k*') AtTime e       ∴⟨ (λ prf i → prf i (<-wellFounded e)) ⟩
    ⇒ asyncₜ e ∈ Dₜ e k*'               ∴⟨ async∈-resp-Dₜ e (sym (trans (ηₛ≡ηₑ-mpp mpp) ηₘ≡ηₑ)) ⟩
    ⇒ asyncₜ e ∈ Dₜ s k*'               ∴⟨ proj₂ (proj₂ (D-finish (η s) (ρ s))) ⟩
    ⇒ asyncₜ e ≈ ξ (η s) (ρ s)          ∎
    where
    k*' = k* (η s) (ρ s)

  ξ-reached : ∀ {s} → ∃ λ k → ∀ {m e} →
            IsMultiPseudoperiodic k [ s , m ] →
            IsSubEpoch [ m , e ] →
            async (<-wellFounded e) ≈ ξ (η s) (ρ s)
  ξ-reached {s} = suc (k* (η s) (ρ s)) , ξ-reached′

isSafe : IsSafeOver 𝓘 D₀
isSafe = record
  { m*         = ξ
  ; m*-reached = ξ-reached
  }
