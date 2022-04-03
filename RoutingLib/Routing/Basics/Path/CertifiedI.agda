open import Data.Fin using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.Maybe as Maybe hiding (module Maybe)
open import Data.Maybe.Relation.Unary.Any as MaybeAny
open import Data.Maybe.Relation.Unary.All as MaybeAll
open import Data.Maybe.Relation.Binary.Pointwise as MaybePointwise using (Pointwise)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; ∃₂; ∃)
open import Level using () renaming (zero to 0ℓ)
open import Relation.Nullary using (¬_)
open import Relation.Binary using (Rel; REL)

import RoutingLib.Routing.Basics.Path.Certified as Certified

module RoutingLib.Routing.Basics.Path.CertifiedI where

private
  variable
    n : ℕ

----------------------------------------------------------------------------
-- Reimports

open Certified public
  using
  ( Edge ; Vertex
  ; [] ; _∷_∣_∣_; _∷_
  ; notHere ; notThere
  ; start ; continue
  ; nonEmpty
  ; ⇨[]⇨; ⇨∷⇨
  )
  renaming
  ( Path    to Pathᵛ
  ; _≈ₚ_    to _≈ᵥₚ_
  ; _∉ₚ_    to _∉ᵥₚ_
  ; _∈ₚ_    to _∈ᵥₚ_
  ; _⇿_     to _⇿ᵛ_
  ; _⇨[_]⇨_ to _⇨[ᵛ_]⇨_
  ; length to lengthᵛ
  )

----------------------------------------------------------------------------
-- The path type

Path : ℕ → Set
Path n = Maybe (Pathᵛ n)

open Maybe          public using () renaming (nothing to invalid; just to valid)
open MaybePointwise public using () renaming (nothing to invalid; just to valid)
open MaybeAll       public using () renaming (nothing to invalid; just to valid; drop-just to drop-valid)
open MaybeAny       public using () renaming (just to valid)

pattern trivial = valid []

----------------------------------------------------------------------------
-- Linkage

infix 4 _⇿_

_⇿_ : Edge n → Path n → Set
e ⇿ p = Any (e ⇿ᵛ_) p

_↮_ : Edge n → Path n → Set
e ↮ p = ¬ (e ⇿ p)

----------------------------------------------------------------------------
-- Membership

infix 4 _∉ₚ_ _∈ₚ_

_∉ₚ_ : Vertex n → Path n → Set
i ∉ₚ p = All (i ∉ᵥₚ_) p

_∈ₚ_ : Vertex n → Path n → Set
i ∈ₚ p = ¬ (i ∉ₚ p)

----------------------------------------------------------------------------
-- Equality

infix 4 _≈ₚ_ _≉ₚ_

_≈ₚ_ : Rel (Path n) 0ℓ
_≈ₚ_ = Pointwise _≈ᵥₚ_

_≉ₚ_ : Rel (Path n) 0ℓ
xs ≉ₚ ys = ¬ (xs ≈ₚ ys)

_≈ₚ_↜_ : Path n → Edge n → Path n → Set
p ≈ₚ e ↜ q = ∃ λ q' → q ≈ₚ valid q' ×
               ∃₂ λ e⇿q e∉q → p ≈ₚ valid (e ∷ q' ∣ e⇿q ∣ e∉q)

------------------------------------------------------------------------------
-- Between

_⇨[_]⇨_ : Fin n → Path n → Fin n → Set
i ⇨[ p ]⇨ j = All (i ⇨[ᵛ_]⇨ j) p

----------------------------------------------------------------------------
-- Operations

length : Path n → ℕ
length = maybe lengthᵛ 0

