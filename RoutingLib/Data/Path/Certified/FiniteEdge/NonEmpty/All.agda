open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Unary using (Pred; _⊆_; Decidable)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Data.Path.Certified.FiniteEdge.NonEmpty

module RoutingLib.Data.Path.Certified.FiniteEdge.NonEmpty.All {n : ℕ} where

----------------------------------------------------------------------------
-- Datatypes

data Allᵥ {p} (P : Pred (Vertex n) p) : Pathⁿᵗ n → Set p where
  []      : Allᵥ P []
  [_,_]∷_ : ∀ {i j p ij⇿p i∉p} → P i → P j → Allᵥ P p → Allᵥ P ((i , j) ∷ p ∣ ij⇿p ∣ i∉p)

data Allₑ {a} (P : Pred (Edge n) a) : Pathⁿᵗ n → Set a where
  []  : Allₑ P []
  _∷_ : ∀ {e p e⇿p e∉p} → P e → Allₑ P p → Allₑ P (e ∷ p ∣ e⇿p ∣ e∉p)

----------------------------------------------------------------------------
-- Operations

module _ {a b} {P : Pred (Vertex n) a} {Q : Pred (Vertex n) b} where

  mapᵥ : P ⊆ Q → Allᵥ P ⊆ Allᵥ Q
  mapᵥ P⊆Q []                = []
  mapᵥ P⊆Q ([ Pi , Pj ]∷ Pp) = [ (P⊆Q Pi) , (P⊆Q Pj) ]∷ (mapᵥ P⊆Q Pp)

module _ {a} {P : Pred (Edge n) a} where

  allₑ? : Decidable P → Decidable (Allₑ P)
  allₑ? P? []                   = yes []
  allₑ? P? (e ∷ p ∣ e⇿p ∣ e∉p) with P? e | allₑ? P? p
  ... | no ¬pe | _      = no λ {(pe ∷ _) → ¬pe pe}
  ... | yes _  | no ¬pp = no λ {(_ ∷ pp) → ¬pp pp}
  ... | yes pe | yes pp = yes (pe ∷ pp)

----------------------------------------------------------------------------
-- Properties

module _ {a} {P : Pred (Fin n) a} where

  Allᵥ-resp-≈ₚ : ∀ {p q} → Allᵥ P p → p ≈ₚ q → Allᵥ P q
  Allᵥ-resp-≈ₚ []                []           = []
  Allᵥ-resp-≈ₚ ([ Pi , Pj ]∷ Pp) (refl ∷ p≈q) = [ Pi , Pj ]∷ Allᵥ-resp-≈ₚ Pp p≈q

module _ {a} {P : Pred (Fin n × Fin n) a} where

  Allₑ-resp-≈ₚ : ∀ {p q} → Allₑ P p → p ≈ₚ q → Allₑ P q
  Allₑ-resp-≈ₚ []          []           = []
  Allₑ-resp-≈ₚ ( i~j ∷ ~p) (refl ∷ p≈q) = i~j ∷ Allₑ-resp-≈ₚ ~p p≈q
