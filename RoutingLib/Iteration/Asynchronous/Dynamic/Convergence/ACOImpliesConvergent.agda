--------------------------------------------------------------------------
-- Agda routing library
--
-- A proof that F being a dynamic ACO implies that the iteration is
-- convergent over the initial box.
--------------------------------------------------------------------------

open import Data.Fin.Subset
  using (Subset; ⊤) renaming (_∈_ to _∈ₛ_; _∉_ to _∉ₛ_)
open import Relation.Unary using (Pred; _⊆_; _∈_)
open import RoutingLib.Relation.Unary.Indexed

open import RoutingLib.Iteration.Asynchronous.Dynamic
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions

module RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.ACOImpliesConvergent
  {a ℓ ℓ₁ ℓ₂ ℓ₃ n}
  (I∥  : AsyncIterable a ℓ n)
  {B₀  : IPred _ ℓ₁}
  {Q   : Pred (Subset n) ℓ₂}
  (aco : PartialACO I∥ B₀ Q ℓ₃)
  where

open import Data.Fin using (Fin)
open import Data.Fin.Dec using (_∈?_)
open import Data.Maybe using (just; nothing)
open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties hiding (_≟_)
open import Data.Product as Prod using (∃; proj₂; proj₁; _,_; _×_; map)
open import Function using (id; _∘_; _$_)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using (<-wellFounded)
open import Level using ()
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality
  using (_≡_; subst; subst₂; cong; cong₂; refl; sym; trans)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Relation.Binary.Indexed.Homogeneous
open import RoutingLib.Relation.Unary.Properties
open import RoutingLib.Function
open import RoutingLib.Function.Reasoning

open import RoutingLib.Iteration.Asynchronous.Dynamic.Properties
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Properties.ACO
  as ACOProperties
open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule
import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule.Pseudoperiod
  as Pseudoperiod

open AsyncIterable I∥
open PartialACO  aco
open ACOProperties I∥ aco

------------------------------------------------------------------------
-- Notation

module _ {x : S} (x∈B₀ : x ∈ᵢ B₀)
         {ψ : Schedule n} (ρ∈Q : ψ satisfies Q)
         where

  open Schedule ψ
  open Pseudoperiod ψ

  -- Some shorthand notation where the epoch and participant indices are
  -- replaced with a time index.

  Fₜ : 𝕋 → S → S
  Fₜ t = F (η t) (ρ t)

  Bₜ : 𝕋 → ℕ → IPred Sᵢ ℓ₃
  Bₜ t = B (η t) (ρ∈Q t)

  δ' : S → ∀ {t} → Acc _<_ t → S
  δ' = asyncIter' I∥ ψ

  δ : S → 𝕋 → S
  δ = asyncIter I∥ ψ
  
  -- Membership substitution for equal times

  δ'∈-resp-Bₜᵢ : ∀ t {s e k} {rec : Acc _<_ t} → η s ≡ η e →
                    ∀ {i} → δ' x rec i ∈ Bₜ s k i → δ' x rec i ∈ Bₜ e k i
  δ'∈-resp-Bₜᵢ t {s} {e} {k} {rec} ηₛ≡ηₑ {i} =
    subst (λ v → δ' x rec i ∈ v k i) (B-subst ηₛ≡ηₑ (cong π ηₛ≡ηₑ) (ρ∈Q s) (ρ∈Q e))

  δ'∈-resp-Bₜ : ∀ t {b s e} {rec : Acc _<_ t} → η s ≡ η e →
                   δ' x rec ∈ᵢ Bₜ s b → δ' x rec ∈ᵢ Bₜ e b
  δ'∈-resp-Bₜ t ηₛ≡ηₑ ∈b i = δ'∈-resp-Bₜᵢ t ηₛ≡ηₑ (∈b i)

  -- The concept of being locally safe

  StateOfNode_InBox_AtTime_ : Fin n → ℕ → 𝕋 → Set ℓ₃
  StateOfNode i InBox k AtTime t = (acc : Acc _<_ t) → δ' x acc i ∈ Bₜ t k i

  StateInBox_AtTime_ : ℕ → 𝕋 → Set ℓ₃
  StateInBox k AtTime t = ∀ i → StateOfNode i InBox k AtTime t

  MessagesToNode_InBox_AtTime_ : Fin n → ℕ → 𝕋 → Set ℓ₃
  MessagesToNode i InBox k AtTime t = ∀ {s} → t < s → SubEpoch [ t , s ] →
                                      ∀ {j} {acc : Acc _<_ (β s i j)} →
                                      δ' x acc j ∈ Bₜ t k j

  MessagesInBox_AtTime_ : ℕ → 𝕋 → Set ℓ₃
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
  i∉ρ⇒state∈Bₖ {i} {t} {k} i∉ρₜ recₑ = begin⟨ B-null (ρ∈Q t) i∉ρₜ ⟩
    ∴ ⊥ i          ∈ Bₜ t k i $⟨ Bᵢ-cong (ρ∈Q t) (≈ᵢ-sym (≈ᵢ-reflexive (asyncIter-inactive I∥ ψ x recₑ i∉ρₜ))) ⟩
    ∴ δ' x {t} _ i ∈ Bₜ t k i ∎

--------------------------------------------------------------------------
-- Base case: the asynchronous iteration is always in the initial box

  state∈B₀ : ∀ t → StateInBox 0 AtTime t
  state∈B₀ zero    i (acc rec) with i ∈? ρ 0
  ... | no  i∉ρ₀ = B-null (ρ∈Q 0) i∉ρ₀
  ... | yes _    = proj₁ (B₀-eqᵢ (ρ∈Q 0)) (x∈B₀ i)
  state∈B₀ (suc t) i (acc rec) with i ∈? ρ (suc t) | i ∈? ρ t | i ∈? α (suc t)
  ... | no  i∉ρ₁₊ₜ  | _     | _     = B-null (ρ∈Q (suc t)) i∉ρ₁₊ₜ
  ... | yes _       | no  _ | _     = proj₁ (B₀-eqᵢ (ρ∈Q (suc t))) (x∈B₀ i)
  ... | yes _       | yes _ | no  _ = B₀ₑ-eqᵢ (ρ∈Q t) (ρ∈Q (suc t)) (state∈B₀ t i (rec t _))
  ... | yes _       | yes _ | yes _ = begin⟨ (λ j → state∈B₀ (β (suc t) i j) j _) ⟩
    ∴ (∀ j → _ ∈ Bₜ (β (suc t) i j) 0 j) $⟨ B₀ₑ-eqᵢ (ρ∈Q _) (ρ∈Q (suc t)) ∘_ ⟩
    ∴ (∀ j → _ ∈ Bₜ (suc t)         0 j) $⟨ (λ prf → F-resp-B₀ₑ (ρ∈Q (suc t)) prf i) ⟩
    ∴ Fₜ (suc t) _ i ∈ Bₜ (suc t)   0 i  ∎

  messages∈B₀ : ∀ t → MessagesInBox 0 AtTime t
  messages∈B₀ t i {s} t<s η[t,s] {j} {accβ} = begin⟨ state∈B₀ (β s i j) j accβ ⟩
    ∴ δ' x accβ j ∈ Bₜ (β s i j) 0 j $⟨ B₀ₑ-eqᵢ (ρ∈Q (β s i j)) (ρ∈Q t) ⟩
    ∴ δ' x accβ j ∈ Bₜ t         0 j ∎

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
  state-stability {k}     {s} {zero}  {i} η[s,1+e]@(mkₛₑ z≤n   _)       (_ , _ , s∈Bₖ)    = s∈Bₖ
  state-stability {zero}  {s} {suc e} {i} η[s,1+e]                      (_ , _ , _)   (acc rec) = state∈B₀ (suc e) i (acc rec)
  state-stability {suc k} {s} {suc e} {i} η[s,1+e]@(mkₛₑ s≤1+e ηₛ≡η₁₊ₑ) (wf , m∈Bₖ , s∈Bₖ) (acc rec) with <-cmp s (suc e)
  ... | tri≈ _ refl _      = s∈Bₖ (acc rec)
  ... | tri> _ _ s>1+e     = contradiction s≤1+e (<⇒≱ s>1+e)
  ... | tri< (s≤s s≤e) _ _ with η-inRange ηₛ≡η₁₊ₑ (s≤e , n≤1+n _)
  ...   | ηₛ≡ηₑ , ηₑ≡η₁₊ₑ with i ∈? ρ (suc e) | i ∈? ρ e | i ∈? α (suc e)
  ...     | no  i∉ρ₁₊ₑ | _       | _     = B-null (ρ∈Q (suc e)) i∉ρ₁₊ₑ
  ...     | yes i∈ρ₁₊ₑ | no i∉ρₑ | _     = contradiction (∈ρ-subst (sym ηₑ≡η₁₊ₑ) i∈ρ₁₊ₑ) i∉ρₑ
  ...     | yes _      | yes _   | no  _ = begin⟨ state-stability (mkₛₑ s≤e ηₛ≡ηₑ) (wf , m∈Bₖ , s∈Bₖ) (rec e ≤-refl) ⟩
    ∴ δ' x {e} _ i ∈ Bₜ e       (suc k) i $⟨ δ'∈-resp-Bₜᵢ e ηₑ≡η₁₊ₑ ⟩
    ∴ δ' x {e} _ i ∈ Bₜ (suc e) (suc k) i ∎
  ...     | yes i∈ρ₁₊ₑ | yes _   | yes _ with ∈ρ-subst (sym ηₛ≡η₁₊ₑ) i∈ρ₁₊ₑ
  ...       | i∈ρₛ = begin⟨ (λ j → m∈Bₖ (s≤s s≤e) η[s,1+e]) ⟩
    ∴ (∀ j → δ' x {β (suc e) i j} _ j ∈ Bₜ s       k      j)  $⟨ (λ prf j → δ'∈-resp-Bₜᵢ (β (suc e) i j) ηₛ≡η₁₊ₑ (prf j)) ⟩
    ∴ (∀ j → δ' x {β (suc e) i j} _ j ∈ Bₜ (suc e) k      j)  $⟨ (λ prf → F-mono-B (ρ∈Q (suc e)) (wf (s≤s s≤e) η[s,1+e]) prf i) ⟩
    ∴ Fₜ (suc e) _ i                  ∈ Bₜ (suc e) (suc k) i  ∎

  state-stability′ : ∀ {k s e} → SubEpoch [ s , e ] →
                    ComputationInBox k AtTime s →
                    StateInBox k AtTime e
  state-stability′ {_} {s} η[s,e]@(mkₛₑ _ ηₛ≡ηₑ) c∈Bₖ i with i ∈? ρ s
  ... | yes i∈ρₛ = state-stability η[s,e] (c∈Bₖ i i∈ρₛ)
  ... | no  i∉ρₛ = i∉ρ⇒state∈Bₖ (i∉ρₛ ∘ ∈ρ-subst (sym ηₛ≡ηₑ))
  
  message-stability : ∀ {k s e i} → SubEpoch [ s , e ] →
                      MessagesToNode i InBox k AtTime s →
                      MessagesToNode i InBox k AtTime e
  message-stability η[s,e]@(mkₛₑ s≤e ηₛ≡ηₑ) m∈b e<t η[e,t] {j} {recβ} =
    δ'∈-resp-Bₜᵢ (β _ _ _) ηₛ≡ηₑ (m∈b (<-transʳ s≤e e<t) (η[s,e] ++ₛₑ η[e,t]))

--------------------------------------------------------------------------
-- Step: after one pseudoperiod the node is guaranteed to have
-- advanced at least one box

  advance-state : ∀ {s e i k} →
                  i IsActiveIn [ s , e ] →
                  MessagesToNode i WellFormedAtTime s →
                  MessagesToNode i InBox k AtTime s →
                  StateOfNode i InBox (suc k) AtTime e
  advance-state {s} {zero}  {i} (mkₐᵢ ηₛ≡η₁₊ₑ m ()  z≤n   i∈αₘ)
  advance-state {s} {suc e} {i} (mkₐᵢ ηₛ≡η₁₊ₑ m s<m m≤1+e i∈αₘ) wf m∈Bₖ (acc recₑ)
    with η-inRange ηₛ≡η₁₊ₑ (≤-pred (≤-trans s<m m≤1+e) , n≤1+n _)
  ... | ηₛ≡ηₑ , ηₑ≡η₁₊ₑ with i ∈? ρ (suc e) | i ∈? ρ e | i ∈? α (suc e)
  ...   | no  i∉ρ₁₊ₑ | _       | _     = B-null (ρ∈Q (suc e)) i∉ρ₁₊ₑ
  ...   | yes i∈ρ₁₊ₑ | no i∉ρₑ | _     = contradiction (∈ρ-subst (sym ηₑ≡η₁₊ₑ) i∈ρ₁₊ₑ) i∉ρₑ
  ...   | yes i∈ρ₁₊ₑ | yes _   | yes _ = F-mono-B (ρ∈Q (suc e)) (wf s<1+e (mkₛₑ s≤1+e ηₛ≡η₁₊ₑ)) (λ j → δ'∈-resp-Bₜᵢ (β (suc e) i j) ηₛ≡η₁₊ₑ (m∈Bₖ s<1+e (mkₛₑ s≤1+e ηₛ≡η₁₊ₑ))) i
    where s<1+e = ≤-trans s<m m≤1+e; s≤1+e = ≤-trans (n≤1+n s) s<1+e
  ...   | yes _       | yes _   | no  i∉α₁₊ₑ with m ≟ℕ suc e
  ...     | yes refl  = contradiction i∈αₘ i∉α₁₊ₑ
  ...     | no  m≢1+e = δ'∈-resp-Bₜᵢ e ηₑ≡η₁₊ₑ (advance-state (mkₐᵢ ηₛ≡ηₑ m s<m m≤e i∈αₘ) wf m∈Bₖ _)
    where m≤e = ≤-pred (≤∧≢⇒< m≤1+e m≢1+e)

  advance-messages : ∀ {s e k i} → MessagesTo i ExpireIn [ s , e ] →
                     ComputationInBox k AtTime s →
                     MessagesToNode i InBox k AtTime e
  advance-messages {s} {e} {k} {i} (mkₑ (mkₛₑ _ ηₛ≡ηₑ) expiryᵢ) c∈Bₖ e<t (mkₛₑ _ ηₑ≡ηₜ) {j} {recβ}
    with trans ηₛ≡ηₑ ηₑ≡ηₜ | expiryᵢ e<t j
  ... | ηₛ≡ηₜ | s≤β with η-inRange ηₛ≡ηₜ (s≤β , (β-decreasing i j (<-transʳ z≤n e<t)))
  ...   | (ηₛ≡ηβ , ηβ≡ηₜ) with trans ηβ≡ηₜ (sym ηₑ≡ηₜ)
  ...     | ηβ≡ηₑ with j ∈? ρ s
  ...       | yes j∈ρₛ = δ'∈-resp-Bₜᵢ (β _ _ _) ηβ≡ηₑ (state-stability (mkₛₑ s≤β ηₛ≡ηβ) (c∈Bₖ j j∈ρₛ) recβ)
  ...       | no  j∉ρₛ = δ'∈-resp-Bₜᵢ (β _ _ _) ηβ≡ηₑ (i∉ρ⇒state∈Bₖ (j∉ρₛ ∘ ∈ρ-subst (sym ηₛ≡ηβ)) recβ)
  
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

  module _ {s e : 𝕋} where

    k*' : ℕ
    k*' = k* (η s) (ρ∈Q s)

    x*' : S
    x*' = x* (η s) (ρ∈Q s)

    B[k*]-reached : MultiPseudocycle k*' [ s , e ] →
                    ∀ {t} → SubEpoch [ e , t ] →
                    δ x t ∈ᵢ Bₜ t k*'
    B[k*]-reached pp {t} η[e,t] with k*' | pp
    ... | zero  | _              = λ i → state∈B₀ t i (<-wellFounded t)
    ... | suc k | next m pp' mpp = begin⟨ computation∈B₁ pp' ⟩
      ∴ ComputationInBox 1       AtTime m   $⟨ advance-computationₙ mpp ⟩
      ∴ ComputationInBox (suc k) AtTime e   $⟨ (λ prf i → state-stability′ η[e,t] prf i (<-wellFounded t)) ⟩
      ∴ δ x t ∈ᵢ Bₜ t (suc k)               ∎
    
    x*-reached : MultiPseudocycle k*' [ s , e ] →
                 ∀ {t} → SubEpoch [ e , t ] →
                 δ x t ≈ x*'
    x*-reached mpp {t} η[e,t] = begin⟨ B[k*]-reached mpp η[e,t] ⟩
      ∴ δ x t ∈ᵢ Bₜ t k*'  $⟨ δ'∈-resp-Bₜ t ηₛ≡ηₜ ⟩
      ∴ δ x t ∈ᵢ Bₜ s k*'  $⟨ k*≤k∧x∈Bₖ⇒x≈x* (η s) (ρ∈Q s) ≤-refl ⟩
      ∴ δ x t ≈ x*'        ∎
      where ηₛ≡ηₜ = sym (trans (ηₛ≡ηₑ-mpp mpp) (SubEpoch.ηₛ≡ηₑ η[e,t]))

convergent : PartiallyConvergent I∥ B₀ Q
convergent = record
  { x*         = x*
  ; k*         = k*
  ; x*-fixed   = x*-fixed
  ; x*-reached = x*-reached
  }
