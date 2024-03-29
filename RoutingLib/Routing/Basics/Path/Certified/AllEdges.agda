open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Unary using (Pred; _⊆_; Decidable)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Routing.Basics.Path.Certified

module RoutingLib.Routing.Basics.Path.Certified.AllEdges {n : ℕ} where

----------------------------------------------------------------------------
-- Datatypes

data Allₑ {a} (P : Pred (Edge n) a) : Path n → Set a where
  []  : Allₑ P []
  _∷_ : ∀ {e p e⇿p e∉p} → P e → Allₑ P p → Allₑ P (e ∷ p ∣ e⇿p ∣ e∉p)

----------------------------------------------------------------------------
-- Operations

module _ {a} {P : Pred (Edge n) a} where

  allₑ? : Decidable P → Decidable (Allₑ P)
  allₑ? P? [] = yes []
  allₑ? P? (e ∷ p ∣ e⇿p ∣ e∉p) with P? e | allₑ? P? p
  ... | no ¬pe | _      = no λ {(pe ∷ _) → ¬pe pe}
  ... | yes _  | no ¬pp = no λ {(_ ∷ pp) → ¬pp pp}
  ... | yes pe | yes pp = yes (pe ∷ pp)

----------------------------------------------------------------------------
-- Properties

module _ {a} {P : Pred (Edge n) a} where

  Allₑ-resp-≈ₚ : ∀ {p q} → Allₑ P p → p ≈ₚ q → Allₑ P q
  Allₑ-resp-≈ₚ []          []           = []
  Allₑ-resp-≈ₚ ( i~j ∷ ~p) (refl ∷ p≈q) = i~j ∷ Allₑ-resp-≈ₚ ~p p≈q
