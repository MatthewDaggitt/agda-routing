open import Data.Fin using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.Maybe as Maybe hiding (module Maybe)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Level using () renaming (zero to 0ℓ)
open import Relation.Nullary using (¬_)
open import Relation.Binary using (Rel; REL)

import RoutingLib.Data.Path.Certified as Certified

module RoutingLib.Data.Path.CertifiedI where

----------------------------------------------------------------------------
-- Reimports

open Certified public
  using
  ( Edge ; Vertex
  ; [] ; _∷_∣_∣_; _∷_
  ; notHere ; notThere
  ; start ; continue
  ; nonEmpty
  )
  renaming
  ( Path to Pathᵛ
  ; _≈ₚ_ to _≈ᵥₚ_
  ; _∉ₚ_  to _∉ᵥₚ_
  ; _∈ₚ_  to _∈ᵥₚ_
  ; _⇿_  to _⇿ᵛ_
  ; length to lengthᵛ
  )

----------------------------------------------------------------------------
-- The path type

Path : ℕ → Set
Path n = Maybe (Pathᵛ n)

open Maybe public using () renaming (nothing to invalid; just to valid)

----------------------------------------------------------------------------
-- Linkage

infix 4 _⇿_

_⇿_ : ∀ {n} → Edge n → Path n → Set
e ⇿ p = Any (e ⇿ᵛ_) p

_↮_ : ∀ {n} → Edge n → Path n → Set
e ↮ p = ¬ (e ⇿ p)

----------------------------------------------------------------------------
-- Membership

infix 4 _∉ₚ_ _∈ₚ_

_∉ₚ_ : ∀ {n} → Vertex n → Path n → Set
i ∉ₚ p = All (i ∉ᵥₚ_) p

_∈ₚ_ : ∀ {n} → Vertex n → Path n → Set
i ∈ₚ p = ¬ (i ∉ₚ p)

----------------------------------------------------------------------------
-- Equality

infix 4 _≈ₚ_ _≉ₚ_

_≈ₚ_ : ∀ {n} → Rel (Path n) 0ℓ
_≈ₚ_ = Eq _≈ᵥₚ_

_≉ₚ_ : ∀ {n} → Rel (Path n) 0ℓ
xs ≉ₚ ys = ¬ (xs ≈ₚ ys)

----------------------------------------------------------------------------
-- Operations

length : ∀ {n} → Path n → ℕ
length = maybe lengthᵛ 0
