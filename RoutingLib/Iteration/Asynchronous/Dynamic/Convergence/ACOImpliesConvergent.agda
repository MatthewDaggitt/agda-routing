open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; ⊤) renaming (_∈_ to _∈ₛ_; _∉_ to _∉ₛ_)
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
  (I∥ : AsyncIterable a ℓ n)
  {ℓ₁ ℓ₂ ℓ₃}
  {B₀ : IPred _ ℓ₁}
  {Q : Pred (Subset n) ℓ₂}
  (aco : PartialACO I∥ B₀ Q ℓ₃)
  where

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
  
  δˡᵒᶜᵃˡ : S → ∀ {t} → Acc _<_ (suc t) → Fin n → S
  δˡᵒᶜᵃˡ x {t} (acc rec) i j = δ' x (rec (β (suc t) i j) (s≤s (β-causality t i j))) j
  
  -- Membership substitution for equal times

  ∈Bₜᵢ-resp-rec : ∀ {t b} (rec₁ rec₂ : Acc _<_ t) →
                  ∀ {i} → δ' x rec₁ i ∈ Bₜ t b i → δ' x rec₂ i ∈ Bₜ t b i
  ∈Bₜᵢ-resp-rec {t} rec₁ rec₂ = Bᵢ-cong (ρ∈Q t) (asyncIter-cong I∥ ψ x rec₁ rec₂ refl _)
  
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

  MessagesToNode_In_AtTime_ : Fin n → IPred Sᵢ ℓ₃ → 𝕋 → Set ℓ₃
  MessagesToNode i In b AtTime t = ∀ {j s} → t < s → SubEpoch [ t , s ] → i ∈ₛ ρ s →
                                   (acc : Acc _<_ (β s i j)) → δ' x acc j ∈ b j

  MessagesIn_AtTime_ : IPred Sᵢ ℓ₃ → 𝕋 → Set ℓ₃
  MessagesIn b AtTime t = ∀ i → MessagesToNode i In b AtTime t


  -- Concept of all messages being the current epoch
  MessagesToNode_WellFormedAt_ : Fin n → 𝕋 → Set ℓ
  MessagesToNode i WellFormedAt t = ∀ {s} → t < s → SubEpoch [ t , s ] →
                                    ∀ {j} {accβ : Acc _<_ (β s i j)} →
                                    i ∈ₛ ρ s → j ∉ₛ ρ s → δ' x accβ j ≈ᵢ ⊥ j

  MessagesWellFormedAt : 𝕋 → Set ℓ
  MessagesWellFormedAt t = ∀ i → MessagesToNode i WellFormedAt t

  
  ComputationAtNode_InBox_AtTime_ : Fin n → ℕ → 𝕋 → Set _
  ComputationAtNode i InBox k AtTime t =
      MessagesToNode i WellFormedAt t
    × MessagesToNode i In (Bₜ t (k ∸ 1)) AtTime t
    × StateOfNode i In (Bₜ t k) AtTime t

  ComputationInBox_AtTime_ : ℕ → 𝕋 → Set _
  ComputationInBox k AtTime t = ∀ {i} → i ∈ₛ ρ t → ComputationAtNode i InBox k AtTime t
  
--------------------------------------------------------------------------
-- Actual proofs
--------------------------------------------------------------------------
-- Not participating
  
  expiry⇒wellFormed : ∀ {s e i} → MessagesTo i ExpireIn [ s , e ] →
                      MessagesToNode i WellFormedAt e
  expiry⇒wellFormed {s} {e} {i} (mkₑ (mkₛₑ s≤e ηₛ≡ηₑ) expᵢ) {t} e<t (mkₛₑ _ ηₑ≡ηₜ) {j} {accβ} i∈ρₜ j∉ρₜ
    with trans ηₛ≡ηₑ ηₑ≡ηₜ | β-decreasing i j (<-transʳ z≤n e<t) 
  ... | ηₛ≡ηₜ | βt≤t = begin⟨ expᵢ e<t j , βt≤t ⟩
    ∴ β t i j ∈ₜ [ s , t ] $⟨ η-inRangeₑ ηₛ≡ηₜ ⟩
    ∴ η (β t i j) ≡ η t    $⟨ (λ prf → j∉ρₜ ∘ ∈ρ-subst prf) ⟩
    ∴ j ∉ₛ ρ (β t i j)     $⟨ asyncIter-inactive I∥ ψ x accβ ⟩
    ∴ δ' x accβ j ≡ ⊥ j    $⟨ ≈ᵢ-reflexive ⟩
    ∴ δ' x accβ j ≈ᵢ ⊥ j   ∎

  i∉ρ⇒state∈Bₖ : ∀ {i t k} → i ∉ₛ ρ t → StateOfNode i In (Bₜ t k) AtTime t
  i∉ρ⇒state∈Bₖ {i} {t} {k} i∉ρₜ recₑ = begin⟨ B-null (ρ∈Q t) i∉ρₜ ⟩
    ∴ ⊥ i          ∈ Bₜ t k i $⟨ Bᵢ-cong (ρ∈Q t) (≈ᵢ-sym (≈ᵢ-reflexive (asyncIter-inactive I∥ ψ x recₑ i∉ρₜ))) ⟩
    ∴ δ' x {t} _ i ∈ Bₜ t k i ∎

--------------------------------------------------------------------------
-- Base case: the asynchronous iteration is always in the initial box

  state∈B₀ : ∀ t → StateIn (Bₜ t 0) AtTime t
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

  messages∈B₀ : ∀ t → MessagesIn (Bₜ t 0) AtTime t
  messages∈B₀ t i {j} {s} t<s η[t,s] i∈ρₛ accβ = begin⟨ state∈B₀ (β s i j) j accβ ⟩
    ∴ δ' x accβ j ∈ Bₜ (β s i j) 0 j $⟨ B₀ₑ-eqᵢ (ρ∈Q (β s i j)) (ρ∈Q t) ⟩
    ∴ δ' x accβ j ∈ Bₜ t         0 j ∎

  wellFormed∈B₀ : ∀ {s e} i → Pseudocycle [ s , e ] → MessagesToNode i WellFormedAt e
  wellFormed∈B₀ i pp = expiry⇒wellFormed (extendExpiry (η-trivial _) (η[m,e] i) (β[s,m] i))
    where open Pseudocycle pp
  
  computation∈B₀ : ∀ {s e} → Pseudocycle [ s , e ] → ComputationInBox 0 AtTime e
  computation∈B₀ {s} {e} pp {i} i∈ρₛ = wellFormed∈B₀ i pp , messages∈B₀ e i , state∈B₀ e i

--------------------------------------------------------------------------
-- Preservation: if the asynchronous iteration is in a box and
-- information recieved is in that box then assuming the epoch is the
-- same, it will still be in that box in the future.
  
  wellFormed-stability : ∀ {s e i} → SubEpoch [ s , e ] →
                         MessagesToNode i WellFormedAt s →
                         MessagesToNode i WellFormedAt e
  wellFormed-stability {s} {e} {i} η[s,e]@(mkₛₑ s≤e _) wf e<t η[e,t] =
    wf (<-transʳ s≤e e<t) (η[s,e] ++ₛₑ η[e,t])

  state-stability : ∀ {k s e i} → SubEpoch [ s , e ] →
                    ComputationAtNode i InBox k AtTime s →
                    StateOfNode i In (Bₜ e k) AtTime e
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
  ...     | yes i∈ρ₁₊ₑ | yes _   | yes _ = begin⟨ (λ j → m∈Bₖ (s≤s s≤e) η[s,1+e] i∈ρ₁₊ₑ _) ⟩
    ∴ (∀ j → δ' x {β (suc e) i j} _ j ∈ Bₜ s       k      j)  $⟨ (λ prf j → δ'∈-resp-Bₜᵢ (β (suc e) i j) ηₛ≡η₁₊ₑ (prf j)) ⟩
    ∴ (∀ j → δ' x {β (suc e) i j} _ j ∈ Bₜ (suc e) k      j)  $⟨ (λ prf → F-mono-B (ρ∈Q (suc e)) (wf (s≤s s≤e) η[s,1+e] i∈ρ₁₊ₑ) prf i) ⟩
    ∴ Fₜ (suc e) _ i                  ∈ Bₜ (suc e) (suc k) i  ∎

  state-stability′ : ∀ {k s e i} → SubEpoch [ s , e ] →
                    (i ∈ₛ ρ s → ComputationAtNode i InBox k AtTime s) →
                    StateOfNode i In (Bₜ e k) AtTime e
  state-stability′ {_} {s} {_} {i} η[s,e]@(mkₛₑ _ ηₛ≡ηₑ) ∈ρ⇒c∈Bₖ with i ∈? ρ s
  ... | yes i∈ρₛ = state-stability η[s,e] (∈ρ⇒c∈Bₖ i∈ρₛ)
  ... | no  i∉ρₛ = i∉ρ⇒state∈Bₖ (i∉ρₛ ∘ ∈ρ-subst (sym ηₛ≡ηₑ)) 

  message-stability : ∀ {k s e i} → SubEpoch [ s , e ] →
                      MessagesToNode i In (Bₜ s k) AtTime s →
                      MessagesToNode i In (Bₜ e k) AtTime e
  message-stability η[s,e]@(mkₛₑ s≤e ηₛ≡ηₑ) m∈b e<t η[e,t] i∈ρ₁₊ₜ recβ =
    δ'∈-resp-Bₜᵢ (β _ _ _) ηₛ≡ηₑ (m∈b (<-transʳ s≤e e<t) (η[s,e] ++ₛₑ η[e,t]) i∈ρ₁₊ₜ recβ)

--------------------------------------------------------------------------
-- Step: after one pseudoperiod the node is guaranteed to have
-- advanced at least one box

  advance-state : ∀ {s e i k} →
                   i IsActiveIn [ s , e ] →
                   MessagesToNode i WellFormedAt s →
                   MessagesToNode i In (Bₜ s k) AtTime s →
                   StateOfNode i In (Bₜ e (suc k)) AtTime e
  advance-state {s} {zero}  {i} (mkₐᵢ ηₛ≡η₁₊ₑ m ()  z≤n   i∈αₘ)
  advance-state {s} {suc e} {i} (mkₐᵢ ηₛ≡η₁₊ₑ m s<m m≤1+e i∈αₘ) wf m∈Bₖ (acc recₑ)
    with η-inRange ηₛ≡η₁₊ₑ (≤-pred (≤-trans s<m m≤1+e) , n≤1+n _)
  ... | ηₛ≡ηₑ , ηₑ≡η₁₊ₑ with i ∈? ρ (suc e) | i ∈? ρ e | i ∈? α (suc e)
  ...   | no  i∉ρ₁₊ₑ | _       | _     = B-null (ρ∈Q (suc e)) i∉ρ₁₊ₑ
  ...   | yes i∈ρ₁₊ₑ | no i∉ρₑ | _     = contradiction (∈ρ-subst (sym ηₑ≡η₁₊ₑ) i∈ρ₁₊ₑ) i∉ρₑ
  ...   | yes i∈ρ₁₊ₑ | yes _   | yes _ = F-mono-B (ρ∈Q (suc e)) (wf s<1+e (mkₛₑ s≤1+e ηₛ≡η₁₊ₑ) i∈ρ₁₊ₑ) (λ j → δ'∈-resp-Bₜᵢ (β (suc e) i j) ηₛ≡η₁₊ₑ (m∈Bₖ s<1+e (mkₛₑ s≤1+e ηₛ≡η₁₊ₑ) i∈ρ₁₊ₑ _)) i
    where s<1+e = ≤-trans s<m m≤1+e; s≤1+e = ≤-trans (n≤1+n s) s<1+e
  ...   | yes _       | yes _   | no  i∉α₁₊ₑ with m ≟ℕ suc e
  ...     | yes refl  = contradiction i∈αₘ i∉α₁₊ₑ
  ...     | no  m≢1+e = δ'∈-resp-Bₜᵢ e ηₑ≡η₁₊ₑ (advance-state (mkₐᵢ ηₛ≡ηₑ m s<m m≤e i∈αₘ) wf m∈Bₖ _)
    where m≤e = ≤-pred (≤∧≢⇒< m≤1+e m≢1+e)

  
  advance-messages : ∀ {s e k i} → MessagesTo i ExpireIn [ s , e ] →
                     ComputationInBox k AtTime s →
                     MessagesToNode i In (Bₜ e k) AtTime e
  advance-messages {s} {e} {k} {i} (mkₑ (mkₛₑ _ ηₛ≡ηₑ) expiryᵢ) c∈Bₖ {j} e<t (mkₛₑ _ ηₑ≡ηₜ) i∈ρₜ recβ
    with trans ηₛ≡ηₑ ηₑ≡ηₜ | expiryᵢ e<t j
  ... | ηₛ≡ηₜ | s≤β with η-inRange ηₛ≡ηₜ (s≤β , (β-decreasing i j (<-transʳ z≤n e<t)))
  ...   | (ηₛ≡ηβ , ηβ≡ηₜ) with trans ηβ≡ηₜ (sym ηₑ≡ηₜ)
  ...     | ηβ≡ηₑ = δ'∈-resp-Bₜᵢ (β _ _ _) ηβ≡ηₑ (state-stability′ (mkₛₑ s≤β ηₛ≡ηβ) c∈Bₖ recβ)
  
  advance-computation₁ : ∀ {s e k} → Pseudocycle [ s , e ] →
                         ComputationInBox k       AtTime s →
                         ComputationInBox (suc k) AtTime e
  advance-computation₁ {s} pp c∈Bₖ {i} i∈ρₑ = m∈wfᵉ , m∈Bₖᵉ , s∈B₁₊ₖ
    where
    open Pseudocycle pp
    m∈wfᵐ  = expiry⇒wellFormed (β[s,m] i)
    m∈wfᵉ  = wellFormed-stability (η[m,e] i) m∈wfᵐ
    m∈Bₖᵐ  = advance-messages (β[s,m] i) c∈Bₖ
    m∈Bₖᵉ  = message-stability (η[m,e] i) m∈Bₖᵐ
    s∈B₁₊ₖ = advance-state (α[m,e] (∈ρ-subst (sym ηₛ≡ηₑ) i∈ρₑ)) m∈wfᵐ m∈Bₖᵐ
    
  advance-computationₙ : ∀ {s e k n} →
                         MultiPseudocycle n [ s , e ] →
                         ComputationInBox k       AtTime s →
                         ComputationInBox (k + n) AtTime e
  advance-computationₙ {_} {_} {k} {_}     none            c∈Bₖ rewrite +-identityʳ k = c∈Bₖ
  advance-computationₙ {s} {e} {k} {suc n} (next m pp mpp) c∈Bₖ = begin⟨ (λ {i} → c∈Bₖ) ⟩
    ∴ ComputationInBox k           AtTime s $⟨ advance-computation₁ pp ⟩
    ∴ ComputationInBox (suc k)     AtTime m $⟨ advance-computationₙ mpp ⟩
    ∴ ComputationInBox (suc k + n) AtTime e $⟨ subst (ComputationInBox_AtTime e) (sym (+-suc k n)) ⟩
    ∴ ComputationInBox (k + suc n) AtTime e ∎

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
    x*-reached (next m pp mpp) {t} η[m,e]@(mkₛₑ m≤e ηₘ≡ηₑ) = begin⟨ (λ {i} → computation∈B₀ pp) ⟩
      ∴ ComputationInBox 0   AtTime m   $⟨ advance-computationₙ mpp ⟩
      ∴ ComputationInBox k*' AtTime e   $⟨ (λ prf i → state-stability′ η[m,e] (prf {i})) ⟩
      ∴ StateIn (Bₜ t k*') AtTime t     $⟨ (λ prf i → prf i (<-wellFounded t)) ⟩
      ∴ δ x t ∈ᵢ Bₜ t k*'               $⟨ δ'∈-resp-Bₜ t ηₛ≡ηₜ ⟩
      ∴ δ x t ∈ᵢ Bₜ s k*'               $⟨ k*≤k∧x∈Bₖ⇒x≈x* (η s) (ρ∈Q s) ≤-refl ⟩
      ∴ δ x t ≈ x*'                     ∎
      where ηₛ≡ηₜ = sym (trans (Pseudocycle.ηₛ≡ηₑ pp) (trans (ηₛ≡ηₑ-mpp mpp) ηₘ≡ηₑ))

convergent : PartiallyConvergent I∥ B₀ Q
convergent = record
  { x*         = x*
  ; k*         = λ e p → suc (k* e p)
  ; x*-fixed   = x*-fixed
  ; x*-reached = x*-reached
  }
