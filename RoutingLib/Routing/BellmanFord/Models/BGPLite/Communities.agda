open import Data.Nat
open import Data.Nat.Properties using (<-isStrictTotalOrder)
open import Data.Bool using (Bool)
open import Relation.Binary
open import Relation.Binary.Lattice using (Minimum)
open import Relation.Binary.PropositionalEquality
open import Level using () renaming (zero to ℓ₀)
import Data.AVL <-isStrictTotalOrder as AVL

module RoutingLib.Routing.BellmanFord.Models.BGPLite.Communities where

abstract

  Community : Set
  Community = ℕ

  CommunitySet : Set
  CommunitySet = AVL.Tree (λ _ → ℕ)

  ∅ : CommunitySet
  ∅ = AVL.empty

  add : Community → CommunitySet → CommunitySet
  add com set = AVL.insert com com set

  remove : Community → CommunitySet → CommunitySet
  remove com set = AVL.delete com set

  _∈?_ : Community → CommunitySet → Bool
  _∈?_ = AVL._∈?_

  -- We assume there is decidable total order over community sets
  
  postulate _≈ᶜˢ_ : Rel CommunitySet ℓ₀

  postulate _≤ᶜˢ_ : Rel CommunitySet ℓ₀
  
  postulate ≤ᶜˢ-minimum : Minimum _≤ᶜˢ_ ∅

  postulate ≤ᶜˢ-isDecTotalOrder : IsDecTotalOrder _≈ᶜˢ_ _≤ᶜˢ_

  postulate ∈-resp-≈ᶜˢ : ∀ c {cs ds} → cs ≈ᶜˢ ds → c ∈? cs ≡ c ∈? ds

  postulate add-cong : ∀ c {cs ds} → cs ≈ᶜˢ ds → add c cs ≈ᶜˢ add c ds

  postulate remove-cong : ∀ c {cs ds} → cs ≈ᶜˢ ds → remove c cs ≈ᶜˢ remove c ds

  -- Re-exporting properties

  open IsDecTotalOrder ≤ᶜˢ-isDecTotalOrder public
    using (module Eq)
    renaming
    ( refl      to ≤ᶜˢ-refl
    ; reflexive to ≤ᶜˢ-reflexive
    ; antisym   to ≤ᶜˢ-antisym
    ; trans     to ≤ᶜˢ-trans
    ; total     to ≤ᶜˢ-total
    ; ≤-respˡ-≈ to ≤ᶜˢ-respˡ-≈ᶜˢ
    ; ≤-respʳ-≈ to ≤ᶜˢ-respʳ-≈ᶜˢ
    )

  open IsDecEquivalence Eq.isDecEquivalence public
    using ()
    renaming
    ( refl  to ≈ᶜˢ-refl
    ; sym   to ≈ᶜˢ-sym
    ; trans to ≈ᶜˢ-trans
    ; _≟_   to _≟ᶜˢ_
    )
