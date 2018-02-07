open import Data.Nat
open import Data.Nat.Properties using (<-isStrictTotalOrder)
open import Data.Bool using (Bool)
open import Relation.Binary
open import Relation.Binary.Lattice using (Minimum)
open import Relation.Binary.PropositionalEquality
open import Level using () renaming (zero to ℓ₀)
import Data.AVL {Key = ℕ} (λ _ → ℕ) <-isStrictTotalOrder as AVL

module RoutingLib.Routing.Models.BGPLite.Communities where

  abstract

    Community : Set
    Community = ℕ

    CommunitySet : Set
    CommunitySet = AVL.Tree

    ∅ : CommunitySet
    ∅ = AVL.empty
    
    add : Community → CommunitySet → CommunitySet
    add com set = AVL.insert com com set

    remove : Community → CommunitySet → CommunitySet
    remove com set = AVL.delete com set

    _∈?_ : Community → CommunitySet → Bool
    _∈?_ = AVL._∈?_


    postulate _≈ᶜˢ_ : Rel CommunitySet ℓ₀

    postulate ≈ᶜˢ-refl : Reflexive _≈ᶜˢ_

    postulate ≈ᶜˢ-sym : Symmetric _≈ᶜˢ_

    postulate ≈ᶜˢ-trans : Transitive _≈ᶜˢ_

    postulate _≟ᶜˢ_ : Decidable _≈ᶜˢ_


    postulate ∈-resp-≈ᶜˢ : ∀ c {cs ds} → cs ≈ᶜˢ ds → c ∈? cs ≡ c ∈? ds
    
    postulate add-cong : ∀ c {cs ds} → cs ≈ᶜˢ ds → add c cs ≈ᶜˢ add c ds

    postulate remove-cong : ∀ c {cs ds} → cs ≈ᶜˢ ds → remove c cs ≈ᶜˢ remove c ds


    postulate _≤ᶜˢ_ : Rel CommunitySet ℓ₀

    postulate ≤ᶜˢ-refl : Reflexive _≤ᶜˢ_

    postulate ≤ᶜˢ-reflexive : _≈ᶜˢ_ ⇒ _≤ᶜˢ_
    
    postulate ≤ᶜˢ-antisym : Antisymmetric _≈ᶜˢ_ _≤ᶜˢ_

    postulate ≤ᶜˢ-trans : Transitive _≤ᶜˢ_

    postulate ≤ᶜˢ-total : Total _≤ᶜˢ_

    postulate ≤ᶜˢ-minimum : Minimum _≤ᶜˢ_ ∅

    postulate ≤ᶜˢ-respˡ-≈ᶜˢ : ∀ {x y z} → y ≈ᶜˢ z → x ≤ᶜˢ y → x ≤ᶜˢ z

    postulate ≤ᶜˢ-respʳ-≈ᶜˢ : ∀ {x y z} → y ≈ᶜˢ z → y ≤ᶜˢ x → z ≤ᶜˢ x
