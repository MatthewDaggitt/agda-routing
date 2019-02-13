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

open import RoutingLib.Iteration.Asynchronous.Dynamic
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions
open import RoutingLib.Iteration.Asynchronous.Dynamic.Properties
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Properties.ACO
  as ACOProperties
open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule
import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule.Pseudoperiod
  as Pseudoperiod


module RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.ACOImpliesConvergent
  {a ℓ n}
  (𝓘 : AsyncIterable a ℓ n)
  {ℓ₁ ℓ₂ ℓ₃}
  {B₀ : IPred _ ℓ₁}
  {Q : Pred (Subset n) ℓ₂}
  (aco : PartialACO 𝓘 B₀ Q ℓ₃)
   where

open AsyncIterable 𝓘
open PartialACO  aco
open ACOProperties 𝓘 aco

------------------------------------------------------------------------
-- Notation

module _ {x : S} (x∈B₀ : x ∈ᵢ B₀)
         {𝓢 : Schedule n} (ρ∈Q : 𝓢 satisfies Q)
         where

  open Schedule 𝓢
  open Pseudoperiod 𝓢

  -- Some shorthand notation where the epoch and participant indices are
  -- replaced with a time index.

  Fₜ : 𝕋 → S → S
  Fₜ t = F (η t) (ρ t)

  Bₜ : 𝕋 → ℕ → IPred Sᵢ ℓ₃
  Bₜ t = B (η t) (ρ∈Q t)

  δ' : S → ∀ {t} → Acc _<_ t → S
  δ' = asyncIter' 𝓘 𝓢

  δ : S → 𝕋 → S
  δ = asyncIter 𝓘 𝓢
  
  δˡᵒᶜᵃˡ : S → ∀ {t} → Acc _<_ (suc t) → Fin n → S
  δˡᵒᶜᵃˡ x {t} (acc rec) i j = δ' x (rec (β (suc t) i j) (s≤s (β-causality t i j))) j
  
  -- Membership substitution for equal times

  ∈Bₜᵢ-resp-rec : ∀ {t b} (rec₁ rec₂ : Acc _<_ t) →
                  ∀ {i} → δ' x rec₁ i ∈ Bₜ t b i → δ' x rec₂ i ∈ Bₜ t b i
  ∈Bₜᵢ-resp-rec {t} rec₁ rec₂ = Bᵢ-cong (ρ∈Q t) (asyncIter-cong 𝓘 𝓢 x rec₁ rec₂ refl _)
  
  δ'∈-resp-Bₜᵢ : ∀ t {s e k} {rec : Acc _<_ t} → η s ≡ η e →
                    ∀ {i} → δ' x rec i ∈ Bₜ s k i → δ' x rec i ∈ Bₜ e k i
  δ'∈-resp-Bₜᵢ t {s} {e} {k} {rec} ηₛ≡ηₑ {i} =
    subst (λ v → δ' x rec i ∈ v k i) (B-subst ηₛ≡ηₑ (cong π ηₛ≡ηₑ) (ρ∈Q s) (ρ∈Q e))

  δ'∈-resp-Bₜ : ∀ t {b s e} {rec : Acc _<_ t} → η s ≡ η e →
                   δ' x rec ∈ᵢ Bₜ s b → δ' x rec ∈ᵢ Bₜ e b
  δ'∈-resp-Bₜ t ηₛ≡ηₑ ∈b i = δ'∈-resp-Bₜᵢ t ηₛ≡ηₑ (∈b i)

  -- The concept of being locally safe

  StateOfNode_In_AtTime_ : Fin n → IPred Sᵢ ℓ₃ → 𝕋 → Set ℓ₃
  StateOfNode i In b AtTime t = (acc : Acc _<_ t) → δ' x acc i ∈ b i

  StateIn_AtTime_ : IPred Sᵢ ℓ₃ → 𝕋 → Set ℓ₃
  StateIn b AtTime t = ∀ i → StateOfNode i In b AtTime t

  MessagesOfNode_In_AtTime_ : Fin n → IPred Sᵢ ℓ₃ → 𝕋 → Set ℓ₃
  MessagesOfNode i In b AtTime t = ∀ {j s} → t < s → SubEpoch [ t , s ] → i ∈ₛ ρ s →
                                   (acc : Acc _<_ (β s i j)) → δ' x acc j ∈ b j

  MessagesIn_AtTime_ : IPred Sᵢ ℓ₃ → 𝕋 → Set ℓ₃
  MessagesIn b AtTime t = ∀ i → MessagesOfNode i In b AtTime t


  -- Concept of all messages being the current epoch
  MessagesWellFormedAt : 𝕋 → Set ℓ
  MessagesWellFormedAt t = ∀ {i s} → t < s → SubEpoch [ t , s ] →
                           ∀ {j} {accβ : Acc _<_ (β s i j)} →
                           i ∈ₛ ρ s → j ∉ₛ ρ s → δ' x accβ j ≈ᵢ ⊥ j

  data ComputationInBox_AtTime_ : ℕ → 𝕋 → Set (ℓ₃ ⊔ ℓ) where
    zeroᵇ : ∀ {t} → MessagesWellFormedAt t →
            StateIn (Bₜ t 0) AtTime t →
            ComputationInBox 0 AtTime t
    sucᵇ  : ∀ {t k} → MessagesWellFormedAt t →
            MessagesIn (Bₜ t k) AtTime t →
            StateIn (Bₜ t (suc k)) AtTime t →
            ComputationInBox (suc k) AtTime t


  c∈Bₖ⇒s∈Bₖ : ∀ {t k} → ComputationInBox k AtTime t → StateIn (Bₜ t k) AtTime t
  c∈Bₖ⇒s∈Bₖ (zeroᵇ _ s∈Bₖ)   = s∈Bₖ
  c∈Bₖ⇒s∈Bₖ (sucᵇ  _ _ s∈Bₖ) = s∈Bₖ

  c∈Bₖ⇒m∈wf : ∀ {t k} → ComputationInBox k AtTime t → MessagesWellFormedAt t
  c∈Bₖ⇒m∈wf (zeroᵇ m∈wf _)   = m∈wf
  c∈Bₖ⇒m∈wf (sucᵇ  m∈wf _ _) = m∈wf

--------------------------------------------------------------------------
-- Actual proofs
--------------------------------------------------------------------------
-- Not participating

  i∉ρ⇒sᵢ∈Bₖᵢ : ∀ {i t k} → i ∉ₛ ρ t → StateOfNode i In (Bₜ t k) AtTime t
  i∉ρ⇒sᵢ∈Bₖᵢ {i} {t} {k} i∉ρₜ recₑ = begin⟨ B-null (ρ∈Q t) i∉ρₜ ⟩
    ⇒ ⊥ i          ∈ Bₜ t k i ∴⟨ Bᵢ-cong (ρ∈Q t) (≈ᵢ-sym (≈ᵢ-reflexive (asyncIter-inactive 𝓘 𝓢 x recₑ i∉ρₜ))) ⟩
    ⇒ δ' x {t} _ i ∈ Bₜ t k i ∎

--------------------------------------------------------------------------
-- Base case: the asynchronous iteration is always in the initial box

  state∈B₀ : ∀ t → StateIn (Bₜ t 0) AtTime t
  state∈B₀ zero    i (acc rec) with i ∈? ρ 0
  ... | no  i∉ρ₀ = B-null (ρ∈Q 0) i∉ρ₀
  ... | yes _    = proj₁ (B₀-eqᵢ (ρ∈Q 0)) (x∈B₀ i)
  state∈B₀ (suc t) i (acc rec) with i ∈? ρ (suc t) | i ∈? ρ t | i ∈? α (suc t)
  ... | no  i∉ρ₁₊ₜ | _     | _     = B-null (ρ∈Q (suc t)) i∉ρ₁₊ₜ
  ... | yes _       | no  _ | _     = proj₁ (B₀-eqᵢ (ρ∈Q (suc t))) (x∈B₀ i)
  ... | yes _       | yes _ | no  _ = B₀ₑ-eqᵢ (ρ∈Q t) (ρ∈Q (suc t)) (state∈B₀ t i (rec t _))
  ... | yes _       | yes _ | yes _ = begin⟨ (λ j → state∈B₀ (β (suc t) i j) j _) ⟩
    ⇒ (∀ j → _ ∈ Bₜ (β (suc t) i j) 0 j) ∴⟨ B₀ₑ-eqᵢ (ρ∈Q _) (ρ∈Q (suc t)) ∘_ ⟩
    ⇒ (∀ j → _ ∈ Bₜ (suc t)         0 j) ∴⟨ (λ prf → F-resp-B₀ₑ (ρ∈Q (suc t)) prf i) ⟩
    ⇒ Fₜ (suc t) _ i ∈ Bₜ (suc t)   0 i  ∎

  expiry⇒wellFormed : ∀ {s e} → ExpiryPeriod [ s , e ] →
                      MessagesWellFormedAt e
  expiry⇒wellFormed {s}  (mkₑ (mkₛₑ s≤e ηₛ≡ηₑ) expᵢ) {i} {t} e<t (mkₛₑ _ ηₑ≡ηₜ) {j} {accβ} i∈ρₜ j∉ρₜ
    with trans ηₛ≡ηₑ ηₑ≡ηₜ
  ... | ηₛ≡ηₜ = begin⟨ expᵢ (∈ρ-subst (sym ηₛ≡ηₜ) i∈ρₜ) e<t j , β-decreasing i j (<-transʳ z≤n e<t) ⟩
    ⇒ β t i j ∈ₜ [ s , t ] ∴⟨ η-inRangeₑ ηₛ≡ηₜ ⟩
    ⇒ η (β t i j) ≡ η t    ∴⟨ (λ prf → j∉ρₜ ∘ ∈ρ-subst prf) ⟩
    ⇒ j ∉ₛ ρ (β t i j)     ∴⟨ asyncIter-inactive 𝓘 𝓢 x accβ ⟩
    ⇒ δ' x accβ j ≡ ⊥ j   ∴⟨ ≈ᵢ-reflexive ⟩
    ⇒ δ' x accβ j ≈ᵢ ⊥ j   ∎

--------------------------------------------------------------------------
-- Preservation: if the asynchronous iteration is in a box and
-- information recieved is in that box then assuming the epoch is the
-- same, it will still be in that box in the future.

  wellFormed-steps : ∀ {s e} → SubEpoch [ s , e ] →
                     MessagesWellFormedAt s →
                     MessagesWellFormedAt e
  wellFormed-steps η[s,e]@(mkₛₑ s≤e _) wf e<t η[e,t] = wf (<-transʳ s≤e e<t) (η[s,e] ++ₛₑ η[e,t])

  state-steps : ∀ {k s e} → SubEpoch [ s , e ] →
                ComputationInBox k AtTime s →
                StateIn (Bₜ e k) AtTime e
  state-steps {k}     {s} {zero}  η[s,1+e]@(mkₛₑ z≤n   _) c∈Bₖ = c∈Bₖ⇒s∈Bₖ c∈Bₖ
  state-steps {zero}  {s} {suc e} η[s,1+e]                c∈Bₖ i (acc rec) = state∈B₀ (suc e) i (acc rec)
  state-steps {suc k} {s} {suc e} η[s,1+e]@(mkₛₑ s≤1+e ηₛ≡η₁₊ₑ) c∈Bₖ@(sucᵇ wf m∈Bₖ _) i (acc rec) with <-cmp s (suc e)
  ... | tri≈ _ refl _      = c∈Bₖ⇒s∈Bₖ c∈Bₖ i (acc rec)
  ... | tri> _ _ s>1+e     = contradiction s≤1+e (<⇒≱ s>1+e)
  ... | tri< (s≤s s≤e) _ _ with η-inRange ηₛ≡η₁₊ₑ (s≤e , n≤1+n _)
  ...   | ηₛ≡ηₑ , ηₑ≡η₁₊ₑ with i ∈? ρ (suc e) | i ∈? ρ e | i ∈? α (suc e)
  ...     | no  i∉ρ₁₊ₑ | _       | _     = B-null (ρ∈Q (suc e)) i∉ρ₁₊ₑ
  ...     | yes i∈ρ₁₊ₑ | no i∉ρₑ | _     = contradiction (∈ρ-subst (sym ηₑ≡η₁₊ₑ) i∈ρ₁₊ₑ) i∉ρₑ
  ...     | yes _       | yes _   | no  _ = begin⟨ state-steps (mkₛₑ s≤e ηₛ≡ηₑ) c∈Bₖ i (rec e ≤-refl) ⟩
    ⇒ δ' x {e} _ i ∈ Bₜ e       (suc k) i ∴⟨ δ'∈-resp-Bₜᵢ e ηₑ≡η₁₊ₑ ⟩
    ⇒ δ' x {e} _ i ∈ Bₜ (suc e) (suc k) i ∎
  ...     | yes i∈ρ₁₊ₑ | yes _   | yes _ = begin⟨ (λ j → m∈Bₖ i (s≤s s≤e) η[s,1+e] i∈ρ₁₊ₑ _) ⟩
    ⇒ (∀ j → δ' x {β (suc e) i j} _ j ∈ Bₜ s       k      j)  ∴⟨ (λ prf j → δ'∈-resp-Bₜᵢ (β (suc e) i j) ηₛ≡η₁₊ₑ (prf j)) ⟩
    ⇒ (∀ j → δ' x {β (suc e) i j} _ j ∈ Bₜ (suc e) k      j)  ∴⟨ (λ prf → F-mono-B (ρ∈Q (suc e)) (wf (s≤s s≤e) η[s,1+e] i∈ρ₁₊ₑ) prf i) ⟩
    ⇒ Fₜ (suc e) _ i                  ∈ Bₜ (suc e) (suc k) i  ∎

  message-steps : ∀ {k s e} → SubEpoch [ s , e ] →
                  MessagesIn (Bₜ s k) AtTime s →
                  MessagesIn (Bₜ e k) AtTime e
  message-steps η[s,e]@(mkₛₑ s≤e ηₛ≡ηₑ) m∈b i e<t η[e,t] i∈ρ₁₊ₜ recβ =
    δ'∈-resp-Bₜᵢ (β _ _ _) ηₛ≡ηₑ (m∈b i (<-transʳ s≤e e<t) (η[s,e] ++ₛₑ η[e,t]) i∈ρ₁₊ₜ recβ)


  start-pp : ∀ {s e} → Pseudocycle [ s , e ] →
             ComputationInBox 0 AtTime e
  start-pp {s} {e} pp = zeroᵇ m∈wfᵉ s∈B₀
    where
    open Pseudocycle pp
    m∈wfᵐ = expiry⇒wellFormed β[s,m]
    m∈wfᵉ = wellFormed-steps η[m,e] m∈wfᵐ
    s∈B₀  = state∈B₀ e
    
--------------------------------------------------------------------------
-- Step: after one pseudoperiod the node is guaranteed to have
-- advanced at least one box
-- (Bₜ s k)

  advance-stateᵢ : ∀ {s e i k} →
                   MessagesWellFormedAt s →
                   i IsActiveIn [ s , e ] →
                   MessagesOfNode i In (Bₜ s k) AtTime s →
                   StateOfNode i In (Bₜ e (suc k)) AtTime e
  advance-stateᵢ {s} {zero}  {i} wf (mkₐᵢ ηₛ≡η₁₊ₑ m ()  z≤n   i∈αₘ)
  advance-stateᵢ {s} {suc e} {i} wf (mkₐᵢ ηₛ≡η₁₊ₑ m s<m m≤1+e i∈αₘ) m∈Bₖ (acc recₑ)
    with η-inRange ηₛ≡η₁₊ₑ (≤-pred (≤-trans s<m m≤1+e) , n≤1+n _)
  ... | ηₛ≡ηₑ , ηₑ≡η₁₊ₑ with i ∈? ρ (suc e) | i ∈? ρ e | i ∈? α (suc e)
  ...   | no  i∉ρ₁₊ₑ | _       | _     = B-null (ρ∈Q (suc e)) i∉ρ₁₊ₑ
  ...   | yes i∈ρ₁₊ₑ | no i∉ρₑ | _     = contradiction (∈ρ-subst (sym ηₑ≡η₁₊ₑ) i∈ρ₁₊ₑ) i∉ρₑ
  ...   | yes i∈ρ₁₊ₑ | yes _   | yes _ = F-mono-B (ρ∈Q (suc e)) (wf s<1+e (mkₛₑ s≤1+e ηₛ≡η₁₊ₑ) i∈ρ₁₊ₑ) (λ j → δ'∈-resp-Bₜᵢ (β (suc e) i j) ηₛ≡η₁₊ₑ (m∈Bₖ s<1+e (mkₛₑ s≤1+e ηₛ≡η₁₊ₑ) i∈ρ₁₊ₑ _)) i
    where s<1+e = ≤-trans s<m m≤1+e; s≤1+e = ≤-trans (n≤1+n s) s<1+e
  ...   | yes _       | yes _   | no  i∉α₁₊ₑ with m ≟ℕ suc e
  ...     | yes refl  = contradiction i∈αₘ i∉α₁₊ₑ
  ...     | no  m≢1+e = δ'∈-resp-Bₜᵢ e ηₑ≡η₁₊ₑ (advance-stateᵢ wf (mkₐᵢ ηₛ≡ηₑ m s<m m≤e i∈αₘ) m∈Bₖ _)
    where m≤e = ≤-pred (≤∧≢⇒< m≤1+e m≢1+e)

  advance-state : ∀ {s e k} → ActivationPeriod [ s , e ] →
                  MessagesWellFormedAt s →
                  MessagesIn (Bₜ s k) AtTime s →
                  StateIn (Bₜ e (suc k)) AtTime e
  advance-state {s} {e} {k} (mkₐ (mkₛₑ _ ηₛ≡ηₑ) activeᵢ) wf m∈Bₖ i with i ∈? ρ s
  ... | no  i∉ρₛ = i∉ρ⇒sᵢ∈Bₖᵢ (i∉ρₛ ∘ ∈ρ-subst (sym ηₛ≡ηₑ))
  ... | yes i∈ρₛ = advance-stateᵢ wf (activeᵢ i∈ρₛ) (m∈Bₖ i)

  advance-messages : ∀ {s e k} → ExpiryPeriod [ s , e ] →
                     ComputationInBox k AtTime s →
                     MessagesIn (Bₜ e k) AtTime e
  advance-messages (mkₑ (mkₛₑ _ ηₛ≡ηₑ) expiryᵢ) c∈Bₖ i {j} e<t (mkₛₑ e≤t ηₑ≡ηₜ) i∈ρₜ recβ
    with trans ηₛ≡ηₑ ηₑ≡ηₜ
  ... | ηₛ≡ηₜ with expiryᵢ (∈ρ-subst (sym ηₛ≡ηₜ) i∈ρₜ) e<t j
  ...   | s≤β with η-inRange ηₛ≡ηₜ (s≤β , (β-decreasing i j (<-transʳ z≤n e<t)))
  ...     | (ηₛ≡ηβ , ηβ≡ηₜ) = δ'∈-resp-Bₜᵢ (β _ _ _) (trans ηβ≡ηₜ (sym ηₑ≡ηₜ)) (state-steps (mkₛₑ s≤β ηₛ≡ηβ) c∈Bₖ j recβ)

  advance-computation₁ : ∀ {s e k} → Pseudocycle [ s , e ] →
                         ComputationInBox k       AtTime s →
                         ComputationInBox (suc k) AtTime e
  advance-computation₁ pp c∈Bₖ = sucᵇ m∈wfᵉ m∈Bₖᵉ s∈B₁₊ₖ
    where
    open Pseudocycle pp
    m∈wfᵐ = wellFormed-steps η[s,m] (c∈Bₖ⇒m∈wf c∈Bₖ)
    m∈wfᵉ  = wellFormed-steps η[m,e] m∈wfᵐ
    m∈Bₖᵐ  = advance-messages β[s,m] c∈Bₖ
    m∈Bₖᵉ  = message-steps η[m,e] m∈Bₖᵐ
    s∈B₁₊ₖ = advance-state α[m,e] m∈wfᵐ m∈Bₖᵐ

  advance-computationₙ : ∀ {s e k n} →
                         MultiPseudocycle n [ s , e ] →
                         ComputationInBox k       AtTime s →
                         ComputationInBox (k + n) AtTime e
  advance-computationₙ {_} {_} {k} {_}     none            c∈Bₖ rewrite +-identityʳ k = c∈Bₖ
  advance-computationₙ {s} {e} {k} {suc n} (next m pp mpp) c∈Bₖ = begin⟨ c∈Bₖ ⟩
    ⇒ ComputationInBox k           AtTime s ∴⟨ advance-computation₁ pp ⟩
    ⇒ ComputationInBox (suc k)     AtTime m ∴⟨ advance-computationₙ mpp ⟩
    ⇒ ComputationInBox (suc k + n) AtTime e ∴⟨ subst (ComputationInBox_AtTime e) (sym (+-suc k n)) ⟩
    ⇒ ComputationInBox (k + suc n) AtTime e ∎

--------------------------------------------------------------------------
-- Convergence

  module _ {s e : 𝕋} where

    k*' : ℕ
    k*' = k* (η s) (ρ∈Q s)

    x*' : S
    x*' = x* (η s) (ρ∈Q s)

    x*-reached : MultiPseudocycle (suc k*') [ s , e ] →
                 ∀ {t} → SubEpoch [ e , t ] →
                 δ x t ≈ x*'
    x*-reached (next m pp mpp) {t} η[m,e]@(mkₛₑ m≤e ηₘ≡ηₑ) = begin⟨ start-pp pp ⟩
      ⇒ ComputationInBox 0   AtTime m   ∴⟨ advance-computationₙ mpp ⟩
      ⇒ ComputationInBox k*' AtTime e   ∴⟨ state-steps η[m,e] ⟩
      ⇒ StateIn (Bₜ t k*') AtTime t     ∴⟨ (λ prf i → prf i (<-wellFounded t)) ⟩
      ⇒ δ x t ∈ᵢ Bₜ t k*'               ∴⟨ δ'∈-resp-Bₜ t ηₛ≡ηₜ ⟩
      ⇒ δ x t ∈ᵢ Bₜ s k*'               ∴⟨ k*≤k∧x∈Bₖ⇒x≈x* (η s) (ρ∈Q s) ≤-refl ⟩
      ⇒ δ x t ≈ x*'                     ∎
      where ηₛ≡ηₜ = sym (trans (Pseudocycle.ηₛ≡ηₑ pp) (trans (ηₛ≡ηₑ-mpp mpp) ηₘ≡ηₑ))

convergent : PartiallyConvergent 𝓘 B₀ Q
convergent = record
  { x*         = x*
  ; k*         = λ e p → suc (k* e p)
  ; x*-fixed   = x*-fixed
  ; x*-reached = x*-reached
  }
