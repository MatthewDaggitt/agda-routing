--------------------------------------------------------------------------
-- Agda routing library
--
-- A proof that F being a dynamic ACO implies that the iteration is
-- convergent over the initial box.
--------------------------------------------------------------------------

open import Data.Fin using (Fin)
open import Data.Fin.Subset
  using (Subset; ⊤) renaming (_∈_ to _∈ₛ_; _∉_ to _∉ₛ_)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Maybe using (just; nothing)
open import Data.Nat renaming (_≟_ to _≟ℕ_) hiding (_⊔_)
open import Data.Nat.Properties hiding (_≟_)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Data.Product as Prod using (∃; proj₂; proj₁; _,_; _×_; map)
open import Function using (id; _∘_; _$_)
open import Level using (_⊔_)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality
  using (_≡_; subst; subst₂; cong; cong₂; refl; sym; trans)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred; _⊆_; _∈_)

open import RoutingLib.Relation.Unary.Indexed
open import RoutingLib.Relation.Binary.Indexed.Homogeneous
open import RoutingLib.Relation.Unary.Properties
open import RoutingLib.Function.Reasoning

open import RoutingLib.Iteration.Asynchronous.Dynamic
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions
open import RoutingLib.Iteration.Asynchronous.Dynamic.Properties
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Properties.ACO
  as ACOProperties
open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule
import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule.Pseudocycle
  as Pseudocycles

module RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.ACOImpliesConvergent
  {a ℓ ℓ₁ ℓ₂ ℓ₃ n}
  (I∥  : AsyncIterable a ℓ n) (open AsyncIterable I∥)
  {X₀  : IPred Sᵢ ℓ₁}
  {Q   : Pred (Epoch × Subset n) ℓ₂}
  (partialACO : PartialACO I∥ X₀ Q ℓ₃)
  where

open PartialACO partialACO
open ACOProperties I∥ partialACO

module _ {e p} .(ep∈Q : (e , p) ∈ Q) where
  open LocalACO (localACO ep∈Q) public

------------------------------------------------------------------------
-- Notation

module _ (ψ : Schedule n)
         {x : S} (x∈X₀ : x ∈ᵢ X₀)               -- Initial state
         where

  open Schedule ψ
  open Pseudocycles ψ

  -- Some shorthand notation where the epoch and participant indices are
  -- replaced with a time index.

  Fₜ : 𝕋 → S → S
  Fₜ t = F (η t) (ρ t)

  c : 𝕋 → Epoch × Subset n
  c t = (η t , ρ t)
  
  δ' : S → ∀ {t} → Acc _<_ t → S
  δ' = asyncIter' I∥ ψ

  δ : S → 𝕋 → S
  δ = asyncIter I∥ ψ

  η-pres-∈Q : ∀ {s e : 𝕋} → η s ≡ η e → c e ∈ Q → c s ∈ Q
  η-pres-∈Q ηₛ≡ηₑ cₑ∈Q rewrite ηₛ≡ηₑ = cₑ∈Q

  η-inRange′ : ∀ {s m e : 𝕋} → η s ≡ η e → m ∈ₜ [ s , e ] → c e ∈ Q → η s ≡ η m × η m ≡ η e × c s ∈ Q × c m ∈ Q
  η-inRange′ ηₛ≡ηₑ m∈[s,e] cₑ∈Q with η-inRange ηₛ≡ηₑ m∈[s,e]
  ... | (ηₛ≡ηₘ , ηₘ≡ηₑ) = ηₛ≡ηₘ , ηₘ≡ηₑ , η-pres-∈Q ηₛ≡ηₑ cₑ∈Q , η-pres-∈Q ηₘ≡ηₑ cₑ∈Q

  -- Membership substitution for equal times

  δ'∈-resp-Bₜᵢ : ∀ t {s e} (cₛ∈Q : c s ∈ Q) (cₑ∈Q : c e ∈ Q) {rec : Acc _<_ t} → η s ≡ η e →
                 ∀ {k i} → δ' x rec i ∈ B cₛ∈Q k i → δ' x rec i ∈ B cₑ∈Q k i
  δ'∈-resp-Bₜᵢ t {s} {e} cₛ∈Q cₑ∈Q {rec} ηₛ≡ηₑ {k} {i} =
    subst (λ v → δ' x rec i ∈ v k i) (B-subst cₛ∈Q cₑ∈Q ηₛ≡ηₑ (cong π ηₛ≡ηₑ))

  -- The concept of being locally safe

  StateOfNode_InBox_AtTime_ : Fin n → ℕ → 𝕋 → Set _
  StateOfNode i InBox k AtTime t = (cₜ∈Q : c t ∈ Q) (acc : Acc _<_ t) → δ' x acc i ∈ B cₜ∈Q k i

  StateInBox_AtTime_ : ℕ → 𝕋 → Set _
  StateInBox k AtTime t = ∀ i → StateOfNode i InBox k AtTime t

  MessagesToNode_InBox_AtTime_ : Fin n → ℕ → 𝕋 → Set _
  MessagesToNode i InBox k AtTime t = (cₜ∈Q : c t ∈ Q) → ∀ {s} → t < s → SubEpoch [ t , s ] →
                                      ∀ {j} {acc : Acc _<_ (β s i j)} → 
                                      δ' x acc j ∈ B cₜ∈Q k j

  MessagesInBox_AtTime_ : ℕ → 𝕋 → Set _
  MessagesInBox k AtTime t = ∀ i → MessagesToNode i InBox k AtTime t

  -- Concept of all messages being the current epoch
  MessagesToNode_WellFormedAtTime_ : Fin n → 𝕋 → Set ℓ
  MessagesToNode i WellFormedAtTime t = ∀ {s} → t < s → SubEpoch [ t , s ] →
                                        ∀ {j} {accβ : Acc _<_ (β s i j)} →
                                        j ∉ₛ ρ s → δ' x accβ j ≈ᵢ ⊥ j

  ComputationAtNode_InBox_AtTime_ : Fin n → ℕ → 𝕋 → Set _
  ComputationAtNode i InBox k AtTime t =
      MessagesToNode i WellFormedAtTime t
    × MessagesToNode i InBox (k ∸ 1) AtTime t
    × StateOfNode i InBox k AtTime t

  ComputationInBox_AtTime_ : ℕ → 𝕋 → Set _
  ComputationInBox k AtTime t = ∀ i → i ∈ₛ ρ t → ComputationAtNode i InBox k AtTime t

--------------------------------------------------------------------------
-- Actual proofs
--------------------------------------------------------------------------
-- Not participating
  
  expiry⇒wellFormed : ∀ {s e i} → MessagesTo i ExpireIn [ s , e ] →
                      MessagesToNode i WellFormedAtTime e
  expiry⇒wellFormed {s} {e} {i} (mkₑ (mkₛₑ s≤e ηₛ≡ηₑ) expᵢ) {t} e<t (mkₛₑ _ ηₑ≡ηₜ) {j} {accβ} j∉ρₜ
    with trans ηₛ≡ηₑ ηₑ≡ηₜ | β-decreasing i j (<-transʳ z≤n e<t) 
  ... | ηₛ≡ηₜ | βt≤t = begin⟨ expᵢ e<t j , βt≤t ⟩
    ∴ β t i j ∈ₜ [ s , t ] $⟨ η-inRangeₑ ηₛ≡ηₜ ⟩
    ∴ η (β t i j) ≡ η t    $⟨ (λ prf → j∉ρₜ ∘ ∈ρ-subst prf) ⟩
    ∴ j ∉ₛ ρ (β t i j)     $⟨ asyncIter-inactive I∥ ψ x accβ ⟩
    ∴ δ' x accβ j ≡ ⊥ j    $⟨ ≈ᵢ-reflexive ⟩
    ∴ δ' x accβ j ≈ᵢ ⊥ j   ∎

  i∉ρ⇒state∈Bₖ : ∀ {i t k} → i ∉ₛ ρ t → StateOfNode i InBox k AtTime t
  i∉ρ⇒state∈Bₖ {i} {t} {k} i∉ρₜ cₜ∈Q recₑ = begin⟨ B-null cₜ∈Q i∉ρₜ ⟩
    ∴ ⊥ i          ∈ B cₜ∈Q k i $⟨ Bᵢ-cong cₜ∈Q (≈ᵢ-sym (≈ᵢ-reflexive (asyncIter-inactive I∥ ψ x recₑ i∉ρₜ))) ⟩
    ∴ δ' x {t} _ i ∈ B cₜ∈Q k i ∎

--------------------------------------------------------------------------
-- Base case: the asynchronous iteration is always in the initial box

  state∈X₀ : ∀ t {accₜ : Acc _<_ t} → δ' x accₜ ∈ᵢ X₀
  state∈X₀ zero    {acc rec} i with i ∈? ρ 0
  ... | no  i∉ρ₀ = ⊥∈X₀ i
  ... | yes _    = x∈X₀ i
  state∈X₀ (suc t) {acc rec} i with i ∈? ρ (suc t) | i ∈? ρ t | i ∈? α (suc t)
  ... | no  i∉ρ₁₊ₜ  | _     | _     = ⊥∈X₀ i
  ... | yes _       | no  _ | _     = x∈X₀ i
  ... | yes _       | yes _ | no  _ = state∈X₀ t i
  ... | yes _       | yes _ | yes _ = F-pres-X₀ (λ j → state∈X₀ (β (suc t) i j) j) i
  
  state∈B₀ : ∀ t → StateInBox 0 AtTime t
  state∈B₀ t i cₜ∈Q rec = X₀⊆B₀ cₜ∈Q (state∈X₀ t i)
  
  messages∈B₀ : ∀ t → MessagesInBox 0 AtTime t
  messages∈B₀ t i cₜ∈Q {s} t<s η[t,s] {j} {accβ} = X₀⊆B₀ cₜ∈Q (state∈X₀ (β s i j) j)

--------------------------------------------------------------------------
-- Preservation: if the asynchronous iteration is in a box and
-- information recieved is in that box then assuming the epoch is the
-- same, it will still be in that box in the future.
  
  wellFormed-stability : ∀ {s e i} → SubEpoch [ s , e ] →
                         MessagesToNode i WellFormedAtTime s →
                         MessagesToNode i WellFormedAtTime e
  wellFormed-stability {s} {e} {i} η[s,e]@(mkₛₑ s≤e _) wf e<t η[e,t] =
    wf (<-transʳ s≤e e<t) (η[s,e] ++ₛₑ η[e,t])

  state-stability : ∀ {k s e i} → SubEpoch [ s , e ] →
                    ComputationAtNode i InBox k AtTime s →
                    StateOfNode i InBox k AtTime e
  state-stability {k}     {s} {zero}  {i} η[s,1+e]@(mkₛₑ z≤n   _)       (_ , _ , s∈Bₖ)                     = s∈Bₖ
  state-stability {zero}  {s} {suc e} {i} η[s,1+e]                      (_ , _ , _)        c₁₊ₑ∈Q (acc rec) =
    state∈B₀ (suc e) i c₁₊ₑ∈Q (acc rec)
  state-stability {suc k} {s} {suc e} {i} η[s,1+e]@(mkₛₑ s≤1+e ηₛ≡η₁₊ₑ) (wf , m∈Bₖ , s∈Bₖ) c₁₊ₑ∈Q (acc rec)
    with <-cmp s (suc e)
  ... | tri≈ _ refl _      = s∈Bₖ c₁₊ₑ∈Q (acc rec)
  ... | tri> _ _ s>1+e     = contradiction s≤1+e (<⇒≱ s>1+e)
  ... | tri< (s≤s s≤e) _ _ with η-inRange′ ηₛ≡η₁₊ₑ (s≤e , n≤1+n _) c₁₊ₑ∈Q
  ...   | ηₛ≡ηₑ , ηₑ≡η₁₊ₑ , cₛ∈Q , cₑ∈Q with i ∈? ρ (suc e) | i ∈? ρ e | i ∈? α (suc e)
  ...     | no  i∉ρ₁₊ₑ | _       | _     = B-null c₁₊ₑ∈Q i∉ρ₁₊ₑ
  ...     | yes i∈ρ₁₊ₑ | no i∉ρₑ | _     = contradiction (∈ρ-subst (sym ηₑ≡η₁₊ₑ) i∈ρ₁₊ₑ) i∉ρₑ
  ...     | yes _      | yes _   | no  _ = begin⟨ state-stability (mkₛₑ s≤e ηₛ≡ηₑ) (wf , m∈Bₖ , s∈Bₖ) cₑ∈Q (rec e ≤-refl) ⟩
    ∴ δ' x {e} _ i ∈ B cₑ∈Q   (suc k) i  $⟨ δ'∈-resp-Bₜᵢ e cₑ∈Q c₁₊ₑ∈Q ηₑ≡η₁₊ₑ ⟩
    ∴ δ' x {e} _ i ∈ B c₁₊ₑ∈Q (suc k) i  ∎
  ...     | yes i∈ρ₁₊ₑ | yes _   | yes _ = begin⟨ (λ j → m∈Bₖ cₛ∈Q (s≤s s≤e) η[s,1+e]) ⟩
    ∴ (∀ j → δ' x {β (suc e) i j} _ j ∈ B cₛ∈Q   k      j)  $⟨ (λ prf j → δ'∈-resp-Bₜᵢ (β (suc e) i j) cₛ∈Q c₁₊ₑ∈Q ηₛ≡η₁₊ₑ (prf j)) ⟩
    ∴ (∀ j → δ' x {β (suc e) i j} _ j ∈ B c₁₊ₑ∈Q k      j)  $⟨ (λ prf → F-mono-B c₁₊ₑ∈Q (λ j → state∈X₀ (β (suc e) i j) j) (wf (s≤s s≤e) η[s,1+e]) prf i) ⟩
    ∴ Fₜ (suc e) _ i                  ∈ B c₁₊ₑ∈Q (suc k) i  ∎

  state-stability′ : ∀ {k s e} → SubEpoch [ s , e ] →
                    ComputationInBox k AtTime s →
                    StateInBox k AtTime e
  state-stability′ {_} {s} η[s,e]@(mkₛₑ _ ηₛ≡ηₑ) c∈Bₖ i with i ∈? ρ s
  ... | yes i∈ρₛ = state-stability η[s,e] (c∈Bₖ i i∈ρₛ)
  ... | no  i∉ρₛ = i∉ρ⇒state∈Bₖ (i∉ρₛ ∘ ∈ρ-subst (sym ηₛ≡ηₑ))
  
  message-stability : ∀ {k s e i} → SubEpoch [ s , e ] →
                      MessagesToNode i InBox k AtTime s →
                      MessagesToNode i InBox k AtTime e
  message-stability η[s,e]@(mkₛₑ s≤e ηₛ≡ηₑ) m∈b cₑ∈Q e<t η[e,t] {j} {recβ} =
    δ'∈-resp-Bₜᵢ (β _ _ _) cₛ∈Q cₑ∈Q ηₛ≡ηₑ (m∈b cₛ∈Q (<-transʳ s≤e e<t) (η[s,e] ++ₛₑ η[e,t]))
    where cₛ∈Q = η-pres-∈Q ηₛ≡ηₑ cₑ∈Q

--------------------------------------------------------------------------
-- Step: after one pseudocycle the node is guaranteed to have
-- advanced at least one box

  advance-state : ∀ {s e i k} →
                  i IsActiveIn [ s , e ] →
                  MessagesToNode i WellFormedAtTime s →
                  MessagesToNode i InBox k AtTime s →
                  StateOfNode i InBox (suc k) AtTime e
  advance-state {s} {zero}  {i} (mkₐᵢ ηₛ≡η₁₊ₑ m ()  z≤n   i∈αₘ)
  advance-state {s} {suc e} {i} (mkₐᵢ ηₛ≡η₁₊ₑ m s<m m≤1+e i∈αₘ) wf m∈Bₖ c₁₊ₑ∈Q (acc recₑ)
    with η-inRange′ ηₛ≡η₁₊ₑ (≤-pred (≤-trans s<m m≤1+e) , n≤1+n _) c₁₊ₑ∈Q
  ... | ηₛ≡ηₑ , ηₑ≡η₁₊ₑ , cₛ∈Q , cₑ∈Q with i ∈? ρ (suc e) | i ∈? ρ e | i ∈? α (suc e)
  ...   | no  i∉ρ₁₊ₑ | _       | _     = B-null c₁₊ₑ∈Q i∉ρ₁₊ₑ
  ...   | yes i∈ρ₁₊ₑ | no i∉ρₑ | _     = contradiction (∈ρ-subst (sym ηₑ≡η₁₊ₑ) i∈ρ₁₊ₑ) i∉ρₑ
  ...   | yes i∈ρ₁₊ₑ | yes _   | yes _ = F-mono-B c₁₊ₑ∈Q (λ j → state∈X₀ (β (suc e) i j) j) (wf s<1+e (mkₛₑ s≤1+e ηₛ≡η₁₊ₑ)) (λ j → δ'∈-resp-Bₜᵢ (β (suc e) i j) cₛ∈Q c₁₊ₑ∈Q ηₛ≡η₁₊ₑ (m∈Bₖ cₛ∈Q s<1+e (mkₛₑ s≤1+e ηₛ≡η₁₊ₑ))) i
    where s<1+e = ≤-trans s<m m≤1+e; s≤1+e = ≤-trans (n≤1+n s) s<1+e
  ...   | yes _       | yes _   | no  i∉α₁₊ₑ with m ≟ℕ suc e
  ...     | yes refl  = contradiction i∈αₘ i∉α₁₊ₑ
  ...     | no  m≢1+e = δ'∈-resp-Bₜᵢ e cₑ∈Q c₁₊ₑ∈Q ηₑ≡η₁₊ₑ (advance-state (mkₐᵢ ηₛ≡ηₑ m s<m m≤e i∈αₘ) wf m∈Bₖ cₑ∈Q _)
    where m≤e = ≤-pred (≤∧≢⇒< m≤1+e m≢1+e)
 
  advance-messages : ∀ {s e k i} → MessagesTo i ExpireIn [ s , e ] →
                     ComputationInBox k AtTime s →
                     MessagesToNode i InBox k AtTime e
  advance-messages {s} {e} {k} {i} (mkₑ (mkₛₑ _ ηₛ≡ηₑ) expiryᵢ) c∈Bₖ cₑ∈Q e<t (mkₛₑ _ ηₑ≡ηₜ) {j} {recβ}
    with expiryᵢ e<t j
  ... | s≤β with η-inRange (trans ηₛ≡ηₑ ηₑ≡ηₜ) (s≤β , (β-decreasing i j (<-transʳ z≤n e<t)))
  ...   | (ηₛ≡ηβ , ηβ≡ηₜ) with trans ηβ≡ηₜ (sym ηₑ≡ηₜ)
  ...     | ηβ≡ηₑ with η-pres-∈Q ηβ≡ηₑ cₑ∈Q
  ...       | β∈Q with j ∈? ρ s
  ...         | yes j∈ρₛ = δ'∈-resp-Bₜᵢ (β _ _ _) β∈Q cₑ∈Q ηβ≡ηₑ (state-stability (mkₛₑ s≤β ηₛ≡ηβ) (c∈Bₖ j j∈ρₛ) β∈Q recβ)
  ...         | no  j∉ρₛ = δ'∈-resp-Bₜᵢ (β _ _ _) β∈Q cₑ∈Q ηβ≡ηₑ (i∉ρ⇒state∈Bₖ (j∉ρₛ ∘ ∈ρ-subst (sym ηₛ≡ηβ)) β∈Q recβ)

  advance-computation₁ : ∀ {s e k} → Pseudocycle [ s , e ] →
                         ComputationInBox k       AtTime s →
                         ComputationInBox (suc k) AtTime e
  advance-computation₁ {s} {e} {k} pp c∈Bₖ i i∈ρₑ = m∈wfᵉ , m∈Bₖᵉ , s∈B₁₊ₖ
    where
    open Pseudocycle pp
    i∈ρₛ   = ∈ρ-subst (sym ηₛ≡ηₑ) i∈ρₑ
    m∈wfᵐ  = expiry⇒wellFormed (β[s,m] i∈ρₛ)
    m∈wfᵉ  = wellFormed-stability (η[m,e] i) m∈wfᵐ
    m∈Bₖᵐ  = advance-messages (β[s,m] i∈ρₛ) c∈Bₖ
    m∈Bₖᵉ  = message-stability (η[m,e] i) m∈Bₖᵐ
    s∈B₁₊ₖ = advance-state (α[m,e] i∈ρₛ) m∈wfᵐ m∈Bₖᵐ

  advance-computationₙ : ∀ {s e k n} →
                         MultiPseudocycle n [ s , e ] →
                         ComputationInBox k       AtTime s →
                         ComputationInBox (k + n) AtTime e
  advance-computationₙ {_} {_} {k} {_}     none            c∈Bₖ rewrite +-identityʳ k = c∈Bₖ
  advance-computationₙ {s} {e} {k} {suc n} (next m pp mpp) c∈Bₖ = begin⟨ c∈Bₖ ⟩
    ∴ ComputationInBox k           AtTime s $⟨ advance-computation₁ pp ⟩
    ∴ ComputationInBox (suc k)     AtTime m $⟨ advance-computationₙ mpp ⟩
    ∴ ComputationInBox (suc k + n) AtTime e $⟨ subst (ComputationInBox_AtTime e) (sym (+-suc k n)) ⟩
    ∴ ComputationInBox (k + suc n) AtTime e ∎

--------------------------------------------------------------------------
-- Convergence

  computation∈B₁ : ∀ {s e} → Pseudocycle [ s , e ] → ComputationInBox 1 AtTime e
  computation∈B₁ {s} {e} pp i i∈ρₑ = m∈wfᵉ , messages∈B₀ e i , s∈B₁
    where
    open Pseudocycle pp
    i∈ρₛ   = ∈ρ-subst (sym ηₛ≡ηₑ) i∈ρₑ
    m∈wfᵐ  = expiry⇒wellFormed (β[s,m] i∈ρₛ)
    m∈wfᵉ  = wellFormed-stability (η[m,e] i) m∈wfᵐ
    s∈B₁   = advance-state (α[m,e] i∈ρₛ) m∈wfᵐ (messages∈B₀ (m i) i)

  module _ {s : 𝕋} (cₛ∈Q : c s ∈ Q)  where

    k*' : ℕ
    k*' = k* cₛ∈Q

    x*' : S
    x*' = x* cₛ∈Q

    private
      mpp+e⇒ηₜ≡ηₛ : ∀ {e k} → MultiPseudocycle k [ s , e ] → ∀ {t} → SubEpoch [ e , t ] → η t ≡ η s
      mpp+e⇒ηₜ≡ηₛ mpp η[e,t] = sym (trans (ηₛ≡ηₑ-mpp mpp) (SubEpoch.ηₛ≡ηₑ η[e,t]))

      mpp+e⇒cₜ∈Q : ∀ {e k} → MultiPseudocycle k [ s , e ] → ∀ {t} → SubEpoch [ e , t ] → c t ∈ Q
      mpp+e⇒cₜ∈Q mpp η[e,t] = η-pres-∈Q (mpp+e⇒ηₜ≡ηₛ mpp η[e,t]) cₛ∈Q
      
    B[k*]-reached : ∀ {e k} (mpp : MultiPseudocycle k [ s , e ]) →
                    ∀ {t} → (se : SubEpoch [ e , t ]) →
                    δ x t ∈ᵢ B (mpp+e⇒cₜ∈Q mpp se) k
    B[k*]-reached {e} {zero}  mpp                   {t} se = λ i → state∈B₀ t i (mpp+e⇒cₜ∈Q mpp se) (<-wellFounded t)
    B[k*]-reached {e} {suc k} mpp@(next m pp' mpp') {t} se = begin⟨ computation∈B₁ pp' ⟩
      ∴ ComputationInBox 1       AtTime m  $⟨ advance-computationₙ mpp' ⟩
      ∴ ComputationInBox (suc k) AtTime e  $⟨ (λ prf i → state-stability′ se prf i cₜ∈Q (<-wellFounded t)) ⟩
      ∴ δ x t ∈ᵢ B _ (suc k)               ∎
      where cₜ∈Q = mpp+e⇒cₜ∈Q mpp se
      
    reachesFP : ∀ {e} → MultiPseudocycle k*' [ s , e ] →
                ∀ {t} → SubEpoch [ e , t ] →
                δ x t ≈ x*'
    reachesFP mpp {t} η[e,t] = begin⟨ B[k*]-reached mpp η[e,t] ⟩
      ∴ δ x t ∈ᵢ B cₜ∈Q k*'  $⟨ δ'∈-resp-Bₜᵢ t cₜ∈Q cₛ∈Q ηₛ≡ηₜ ∘_ ⟩
      ∴ δ x t ∈ᵢ B cₛ∈Q k*'  $⟨ k*≤k∧x∈Bₖ⇒x≈x* cₛ∈Q ≤-refl ⟩
      ∴ δ x t ≈ x*'          ∎
      where
      ηₛ≡ηₜ = mpp+e⇒ηₜ≡ηₛ mpp η[e,t]
      cₜ∈Q   = η-pres-∈Q ηₛ≡ηₜ cₛ∈Q

convergent : PartiallyConvergent I∥ X₀ Q
convergent = record
  { localFP   = localFP
  ; reachesFP = reachesFP
  }
