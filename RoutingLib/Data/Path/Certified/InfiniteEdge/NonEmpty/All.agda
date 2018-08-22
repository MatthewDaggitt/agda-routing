open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Unary using (Pred; _⊆_; Decidable)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Data.Path.EdgePath.NonEmpty
open import RoutingLib.Data.Path.EdgePath.NonEmpty.Relation.Equality

module RoutingLib.Data.Path.EdgePath.NonEmpty.All where

  ----------------------------------------------------------------------------
  -- Datatypes

  data Allₙ {a} (P : Pred ℕ a) : Pathⁿᵗ → Set a where
    []      : Allₙ P []
    [_,_]∷_ : ∀ {i j p ij⇿p i∉p} → P i → P j → Allₙ P p → Allₙ P ((i , j) ∷ p ∣ ij⇿p ∣ i∉p)

  data Allₑ {a} (P : Pred (ℕ × ℕ) a) : Pathⁿᵗ → Set a where
    []  : Allₑ P []
    _∷_ : ∀ {e p e⇿p e∉p} → P e → Allₑ P p → Allₑ P (e ∷ p ∣ e⇿p ∣ e∉p)

  ----------------------------------------------------------------------------
  -- Operations

  mapₙ : ∀ {a b} {P : Pred ℕ a} {Q : Pred ℕ b} →
        P ⊆ Q → Allₙ P ⊆ Allₙ Q
  mapₙ P⊆Q []                = []
  mapₙ P⊆Q ([ Pi , Pj ]∷ Pp) = [ (P⊆Q Pi) , (P⊆Q Pj) ]∷ (mapₙ P⊆Q Pp)

  allₑ? : ∀ {a} {P : Pred (ℕ × ℕ) a} →
          Decidable P → Decidable (Allₑ P)
  allₑ? P? []                   = yes []
  allₑ? P? (e ∷ p ∣ e⇿p ∣ e∉p) with P? e | allₑ? P? p
  ... | no ¬pe | _      = no λ {(pe ∷ _) → ¬pe pe}
  ... | _      | no ¬pp = no λ {(_ ∷ pp) → ¬pp pp}
  ... | yes pe | yes pp = yes (pe ∷ pp)

  ----------------------------------------------------------------------------
  -- Properties

  module _ {a} {P : Pred ℕ a} where

    Allₙ-resp-≈ₚ : ∀ {p q} → Allₙ P p → p ≈ₚ q → Allₙ P q
    Allₙ-resp-≈ₚ []                []           = []
    Allₙ-resp-≈ₚ ([ Pi , Pj ]∷ Pp) (refl ∷ p≈q) = [ Pi , Pj ]∷ Allₙ-resp-≈ₚ Pp p≈q

  module _ {a} {P : Pred (ℕ × ℕ) a} where

    Allₑ-resp-≈ₚ : ∀ {p q} → Allₑ P p → p ≈ₚ q → Allₑ P q
    Allₑ-resp-≈ₚ []          []           = []
    Allₑ-resp-≈ₚ ( i~j ∷ ~p) (refl ∷ p≈q) = i~j ∷ Allₑ-resp-≈ₚ ~p p≈q
