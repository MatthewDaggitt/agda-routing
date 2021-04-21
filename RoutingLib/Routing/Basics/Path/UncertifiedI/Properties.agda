open import Data.Maybe
import Data.Maybe.Relation.Unary.Any as Any
import Data.Maybe.Relation.Unary.All as All
open import Data.Nat using (ℕ; suc; z≤n; s≤s) renaming (_≟_ to _≟ℕ_; _≤?_ to _≤ℕ?_; _≤_ to _≤ℕ_; _<_ to _<ℕ_)
open import Data.Nat.Properties using (<-trans; ≤-trans; m≢1+m+n; <⇒≢; <⇒≯; ≤-refl; m+n≮n; suc-injective; <-cmp)
open import Data.Fin using (Fin; _<_; _≤?_; suc; zero)
open import Data.Fin.Properties using (cmp; ≤-antisym; ≤-total; _<?_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; _×_)
open import Level using () renaming (zero to 0ℓ)
open import Relation.Binary using (Decidable; Total; _⇒_; Reflexive; Symmetric; Antisymmetric; Transitive; _Respects_; tri≈; tri<; tri>; IsEquivalence; IsDecEquivalence; Setoid; DecSetoid; _Preserves_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong; isEquivalence)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Routing.Basics.Path.UncertifiedI
import RoutingLib.Routing.Basics.Path.Uncertified.Properties as UncertifiedProperties

module RoutingLib.Routing.Basics.Path.UncertifiedI.Properties where

open UncertifiedProperties public
  using ()
  renaming
  ( _⇿?_        to _⇿ᵥ?_
  ; _∈ₚ?_       to _∈ᵥₚ?_
  ; ⇿-resp-≈ₚ   to ⇿ᵥ-resp-≈ᵥₚ
  ; ∉ₚ-resp-≈ₚ  to ∉ᵥₚ-resp-≈ᵥₚ
  ; p≉i∷p       to p≉ᵛi∷p
  ; ℙₛ          to ℙᵛₛ
  )

open import Data.Maybe.Properties public
  using ()
  renaming
  ( just-injective to valid-injective
  )

----------------------------------------------------------------------------
-- Linkage

infix 4 _⇿?_

_⇿?_ : Decidable _⇿_
e ⇿? p = Any.dec (e ⇿ᵥ?_) p

⇿-resp-≡ : ∀ {e} → (e ⇿_) Respects _≡_
⇿-resp-≡ refl e⇿p = e⇿p

----------------------------------------------------------------------------
-- Membership

_∈ₚ?_ : Decidable _∈ₚ_
k ∈ₚ? p = All.dec (k ∈ᵥₚ?_) p

∈ₚ-resp-≡ : ∀ {k} → (k ∈ₚ_) Respects _≡_
∈ₚ-resp-≡ refl k∈p = k∈p

-- ∉ₚ-resp-≈ : ∀ {k : Fin n} → (k ∈_) Respects _≈ₚ_
-- ∉ₚ-resp-≈ x≈y k∈x k∉y = k∈x (∉-resp-≈ₚ {!≈ₚ-sym ?!} k∉y)

----------------------------------------------------------------------------
-- Equality

p≢i∷p : ∀ {e : Edge} {p : Pathᵛ} → _≢_ {A = Path} (valid p) (valid (e ∷ p))
p≢i∷p {e} eq = p≉ᵛi∷p (valid-injective eq)

{-
  _≟ₚ_ : Decidable (_≈ₚ_ {n})
  invalid ≟ₚ invalid = yes invalid
  invalid ≟ₚ valid q = no λ()
  valid p ≟ₚ invalid  = no λ()
  valid p ≟ₚ valid q with NEP._≟ₚ_ p q
  ... | no  p≉q = no (λ{(valid p≈q) → p≉q p≈q})
  ... | yes p≈q = yes (valid p≈q)
-}

≡-isEquivalence : IsEquivalence _≡_
≡-isEquivalence = isEquivalence {A = Path}
{-
  ≈ₚ-isDecEquivalence : IsDecEquivalence (_≈ₚ_ {n})
  ≈ₚ-isDecEquivalence = record
    { isEquivalence = ≈ₚ-isEquivalence
    ; _≟_           = _≟ₚ_
    }
-}
ℙₛ : Setoid 0ℓ 0ℓ
ℙₛ = record { isEquivalence = ≡-isEquivalence }
{-
  ℙₛ? : DecSetoid 0ℓ 0ℓ
  ℙₛ? = record { isDecEquivalence = ≈ₚ-isDecEquivalence }
-}
