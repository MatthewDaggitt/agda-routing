open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; ⊥)
open import Data.Fin.Dec using () renaming (_∈?_ to _∈ₛ?_)
open import Data.Vec using (_[_]≔_; toList)
open import Data.Bool using (Bool; true; false; _≟_)
open import Data.List.Relation.Lex.Strict using (Lex-≤)
open import Function using (_on_)
open import Relation.Binary
open import Relation.Binary.Lattice using (Minimum)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Level using () renaming (zero to ℓ₀)

open import RoutingLib.Data.Vec.Relation.Lex using (Lex; ≤-isDecTotalOrder; ≤-minimum)
open import RoutingLib.Data.Bool

module RoutingLib.Routing.BellmanFord.Models.BGPLite.Communities where

abstract

  Community : Set
  Community = Fin 32

  CommunitySet : Set
  CommunitySet = Subset 32

  ∅ : CommunitySet
  ∅ = ⊥

  add : Community → CommunitySet → CommunitySet
  add c cs = cs [ c ]≔ true

  remove : Community → CommunitySet → CommunitySet
  remove c cs = cs [ c ]≔ false

  _∈?_ : Community → CommunitySet → Bool
  c ∈? cs = ⌊ c ∈ₛ? cs ⌋

  -- We assume there is decidable total order over community sets
  
  _≈ᶜˢ_ : Rel CommunitySet ℓ₀
  _≈ᶜˢ_ = _≡_
  
  _≤ᶜˢ_ : Rel CommunitySet ℓ₀
  _≤ᶜˢ_ = Lex _<_
  
  ≤ᶜˢ-minimum : Minimum _≤ᶜˢ_ ∅
  ≤ᶜˢ-minimum = ≤-minimum _<_ _≟_ <-minimum
  
  ≤ᶜˢ-isDecTotalOrder : IsDecTotalOrder _≈ᶜˢ_ _≤ᶜˢ_
  ≤ᶜˢ-isDecTotalOrder = ≤-isDecTotalOrder _<_ <-isStrictTotalOrder
  
  ∈-resp-≈ᶜˢ : ∀ c {cs ds} → cs ≈ᶜˢ ds → c ∈? cs ≡ c ∈? ds
  ∈-resp-≈ᶜˢ c refl = refl
  
  add-cong : ∀ c {cs ds} → cs ≈ᶜˢ ds → add c cs ≈ᶜˢ add c ds
  add-cong c refl = refl
  
  remove-cong : ∀ c {cs ds} → cs ≈ᶜˢ ds → remove c cs ≈ᶜˢ remove c ds
  remove-cong c refl = refl
  
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
