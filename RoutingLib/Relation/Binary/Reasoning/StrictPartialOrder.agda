open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_) renaming (refl to ≡-refl)
open import Level using (_⊔_)
open import Data.Product using (proj₁; proj₂)

module RoutingLib.Relation.Binary.Reasoning.StrictPartialOrder
  {a ℓ₁ ℓ₂} (poset : Poset a ℓ₁ ℓ₂) where

  import RoutingLib.Relation.Binary.Reasoning.StrictCore as Core
  import RoutingLib.Relation.Binary.NonStrictToStrict.PartialOrder as Strict

  open Poset poset
  open Strict poset

  infix  4 _IsRelatedTo₁_ _IsRelatedTo₂_
  infix  3 _∎
  infixr 2 _<⟨_⟩<_ _<⟨_⟩≤_ _≤⟨_⟩<_ _≤⟨_⟩≤_ _≈⟨_⟩≤_ _≈⟨_⟩<_ _≡⟨_⟩≤_ _≡⟨_⟩<_
  infix  1 begin_

  -- This seemingly unnecessary type is used to make it possible to
  -- infer arguments even if the underlying equality evaluates.

  data _IsRelatedTo₁_ (x y : Carrier) : Set ℓ₂ where
    relTo₁ : (x≤y : x ≤ y) → x IsRelatedTo₁ y

  data _IsRelatedTo₂_ (x y : Carrier) : Set (ℓ₂ ⊔ ℓ₁) where
    relTo₂ : (x<y : x < y) → x IsRelatedTo₂ y

  begin_ : ∀ {x y} → x IsRelatedTo₂ y → x < y
  begin relTo₂ x<y = x<y

  _≤⟨_⟩≤_ : ∀ x {y z} → x ≤ y → y IsRelatedTo₁ z → x IsRelatedTo₁ z
  _ ≤⟨ x≤y ⟩≤ relTo₁ y≤z = relTo₁ (trans x≤y y≤z)

  _≤⟨_⟩<_ : ∀ x {y z} → x ≤ y → y IsRelatedTo₂ z → x IsRelatedTo₂ z
  _ ≤⟨ x≤y ⟩< relTo₂ y<z = relTo₂ (≤-<-trans x≤y y<z)

  _<⟨_⟩<_ : ∀ x {y z} → x < y → y IsRelatedTo₂ z → x IsRelatedTo₂ z
  _ <⟨ x∼y ⟩< relTo₂ y∼z = relTo₂ (<-trans x∼y y∼z)

  _<⟨_⟩≤_ : ∀ x {y z} → x < y → y IsRelatedTo₁ z → x IsRelatedTo₂ z
  _ <⟨ x∼y ⟩≤ relTo₁ y∼z = relTo₂ (<-≤-trans x∼y y∼z)



  _≈⟨_⟩≤_ : ∀ x {y z} → x ≈ y → y IsRelatedTo₁ z → x IsRelatedTo₁ z
  _ ≈⟨ x≈y ⟩≤ relTo₁ y∼z = relTo₁ (trans (reflexive x≈y) y∼z)

  _≈⟨_⟩<_ : ∀ x {y z} → x ≈ y → y IsRelatedTo₂ z → x IsRelatedTo₂ z
  _ ≈⟨ x≈y ⟩< relTo₂ y∼z = relTo₂ (proj₂ <-resp-≈ (Eq.sym x≈y) y∼z)

  _≡⟨_⟩≤_ : ∀ x {y z} → x ≡ y → y IsRelatedTo₁ z → x IsRelatedTo₁ z
  _ ≡⟨ ≡-refl ⟩≤ relTo₁ y∼z = relTo₁ y∼z

  _≡⟨_⟩<_ : ∀ x {y z} → x ≡ y → y IsRelatedTo₂ z → x IsRelatedTo₂ z
  _ ≡⟨ ≡-refl ⟩< relTo₂ y∼z = relTo₂ y∼z

  _∎ : ∀ x → x IsRelatedTo₁ x
  _∎ _ = relTo₁ refl
