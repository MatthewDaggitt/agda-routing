open import Algebra.Core
open import Data.Product using (_,_)
open import Relation.Binary using (Setoid)

module RoutingLib.Algebra.Definitions.Consequences {a ℓ} (S : Setoid a ℓ) where

open Setoid S renaming (Carrier to A)
open import Algebra.Definitions _≈_
open import Relation.Binary.Reasoning.Setoid S

private
  variable
    e f : A
    _•_ : Op₂ A

idˡ+zeˡ⇒singleton : LeftIdentity e _•_ → LeftZero e _•_ → ∀ x y → x ≈ y
idˡ+zeˡ⇒singleton {e} {_•_} id ze x y = begin
  x      ≈˘⟨ id x ⟩
  e • x  ≈⟨  ze x ⟩
  e      ≈˘⟨ ze y ⟩
  e • y  ≈⟨  id y ⟩
  y      ∎

idʳ+zeʳ⇒singleton : RightIdentity e _•_ → RightZero e _•_ → ∀ x y → x ≈ y
idʳ+zeʳ⇒singleton {e} {_•_} id ze x y = begin
  x      ≈˘⟨ id x ⟩
  x • e  ≈⟨  ze x ⟩
  e      ≈˘⟨ ze y ⟩
  y • e  ≈⟨  id y ⟩
  y      ∎

id+ze⇒singleton : Identity e _•_ → Zero e _•_ → ∀ x y → x ≈ y
id+ze⇒singleton {_} {_•_} (id , _) (ze , _) = idˡ+zeˡ⇒singleton {_•_ = _•_} id ze
