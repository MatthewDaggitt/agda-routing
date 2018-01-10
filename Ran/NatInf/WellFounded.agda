-- imports
open import NatInf
open import Data.Nat
  using (ℕ; zero; suc) renaming (_<′_ to _<'ℕ_; _≤′_ to _≤'ℕ_; _<_ to _<ℕ_;
    ≤′-refl to ≤'ℕ-refl; ≤′-step to ≤'ℕ-step)
open import Data.Nat.Properties
  using () renaming (≤-reflexive to ≤ℕ-reflexive; ≤⇒≤′ to ≤⇒≤'ℕ)
open import Induction
  using (RecStruct)
open import Induction.WellFounded as wf
  --using (Acc; acc; WfRec; Well-founded)
open import Relation.Binary
  using (Rel; _⇒_)
open import Level
  using () renaming (zero to lzero)
open import Relation.Nullary
  using (¬_; yes; no)
open import Relation.Nullary.Negation
  using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (refl)
open import Induction.Nat
  using () renaming (<′-well-founded to <'ℕ-wf)

module NatInf.WellFounded where

  ≤'⇒≤'ℕ : ∀ {m n} → N m ≤' N n → m ≤'ℕ n
  ≤'⇒≤'ℕ ≤'-refl = ≤'ℕ-refl
  ≤'⇒≤'ℕ (≤'-step m≤'n) = ≤'ℕ-step (≤'⇒≤'ℕ m≤'n)

  -- Complete induction based on _<'_
  <'-Rec : ∀ {ℓ} → RecStruct ℕ∞ ℓ ℓ
  <'-Rec = WfRec _<'_

  r : ∀ n → Acc _<'ℕ_ n → WfRec _<'_ (Acc _<'_) (N n)
  r zero (acc rs) ∞ ()
  r zero (acc rs) (N x) ()
  r (suc n) (acc rs) ∞ ()
  r (suc n) (acc rs) (N .n) ≤'-refl =
         acc (r n (rs n (≤⇒≤'ℕ (≤ℕ-reflexive refl))))
  r (suc n) (acc rs) (N x) (≤'-step y<n) =
         acc (r x (rs x (≤'⇒≤'ℕ (≤'-step y<n))))


  mutual
    <'-well-founded : Well-founded _<'_
    <'-well-founded n = acc (<'-well-founded' n)

    <'-well-founded' : ∀ n → <'-Rec (Acc _<'_) n
    <'-well-founded' ∞ ∞ ()
    <'-well-founded' ∞ (N m) ≤'-∞ = acc (r m (<'ℕ-wf m))
    <'-well-founded' (N x) ∞ ()
    <'-well-founded' (N .(suc m)) (N m) ≤'-refl = <'-well-founded (N m)
    <'-well-founded' (N (suc n)) (N m) (≤'-step m<n) = <'-well-founded' (N n) (N m) m<n
