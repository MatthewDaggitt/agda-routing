open import Data.Fin using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.Maybe as Maybe hiding (module Maybe)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Level using () renaming (zero to 0ℓ)
open import Relation.Nullary using (¬_)
open import Relation.Binary using (Rel; REL)
open import Relation.Binary.PropositionalEquality using (_≡_)

import RoutingLib.Data.Path.Uncertified as Uncertified

module RoutingLib.Data.Path.UncertifiedI where

----------------------------------------------------------------------------
-- Reimports

open Uncertified public
  using
  ( Edge ; Vertex
  ; [] ; _∷_
  ; start ; continue
  )
  renaming
  ( Path   to Pathᵛ
  ; _∉ₚ_   to _∉ᵥₚ_
  ; _∈ₚ_   to _∈ᵥₚ_
  ; _⇿_    to _⇿ᵥ_
  ; length to lengthᵥ
  ; source to sourceᵥ
  )

----------------------------------------------------------------------------
-- The path type

Path : Set
Path = Maybe Pathᵛ

open Maybe public using () renaming (nothing to invalid; just to valid)

----------------------------------------------------------------------------
-- Linkage

infix 4 _⇿_

_⇿_ : Edge → Path → Set
e ⇿ p = Any (e ⇿ᵥ_) p

_↮_ : Edge → Path → Set
e ↮ p = ¬ (e ⇿ p)

----------------------------------------------------------------------------
-- Membership

infix 4 _∉ₚ_ _∈ₚ_

_∈ₚ_ : Vertex → Path → Set
i ∈ₚ p = All (i ∈ᵥₚ_) p

_∉ₚ_ : Vertex → Path → Set
i ∉ₚ p = ¬ (i ∈ₚ p)

----------------------------------------------------------------------------
-- Operations

length : Path → ℕ
length invalid   = 0
length (valid p) = lengthᵥ p

source : Path → Maybe ℕ
source invalid   = nothing
source (valid p) = sourceᵥ p
