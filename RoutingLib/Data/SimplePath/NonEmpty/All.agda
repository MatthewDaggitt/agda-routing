open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Unary using (Pred)


open import RoutingLib.Data.SimplePath.NonEmpty
open import RoutingLib.Data.SimplePath.NonEmpty.Relation.Equality

module RoutingLib.Data.SimplePath.NonEmpty.All {n : ℕ} where

  data All {p} (P : Pred (Fin n) p) : SimplePathⁿᵗ n → Set p where
    []      : All P []
    [_,_]∷_ : ∀ {i j p ij⇿p i∉p} → P i → P j → All P p → All P ((i , j) ∷ p ∣ ij⇿p ∣ i∉p)

  
  module _ {a} {P : Pred (Fin n) a} where
  
    All-resp-≈ₚ : ∀ {p q} → All P p → p ≈ₚ q → All P q
    All-resp-≈ₚ []                []           = []
    All-resp-≈ₚ ([ Pi , Pj ]∷ Pp) (refl ∷ p≈q) = [ Pi , Pj ]∷ All-resp-≈ₚ Pp p≈q
