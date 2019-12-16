open import Relation.Binary using (Setoid)
open import Data.Product using (_,_)

module RoutingLib.Algebra.Definitions.Consequences {a ℓ} (S : Setoid a ℓ) where

open Setoid S renaming (Carrier to A)
open import Algebra.FunctionProperties _≈_
open import Relation.Binary.EqReasoning S

module _ {_•_ : Op₂ A} {e f : A} where

  idˡ-subst : Congruent₂ _•_ → LeftIdentity e _•_ → e ≈ f → LeftIdentity f _•_
  idˡ-subst cong id e≈f x = begin
    f • x ≈⟨ cong (sym e≈f) refl ⟩
    e • x ≈⟨ id x ⟩
    x     ∎

  idʳ-subst : Congruent₂ _•_ → RightIdentity e _•_ → e ≈ f → RightIdentity f _•_
  idʳ-subst cong id e≈f x = begin
    x • f ≈⟨ cong refl (sym e≈f) ⟩
    x • e ≈⟨ id x ⟩
    x     ∎

  id-subst : Congruent₂ _•_ → Identity e _•_ → e ≈ f → Identity f _•_
  id-subst cong (idˡ , idʳ) e≈f = idˡ-subst cong idˡ e≈f , idʳ-subst cong idʳ e≈f

idˡ+zeˡ⇒singleton : ∀ {_•_ e} → LeftIdentity e _•_ → LeftZero e _•_ →
                   ∀ x y → x ≈ y
idˡ+zeˡ⇒singleton {_•_} {e} id ze x y = begin
  x     ≈⟨ sym (id x) ⟩
  e • x ≈⟨ ze x ⟩
  e     ≈⟨ sym (ze y) ⟩
  e • y ≈⟨ id y ⟩
  y     ∎

idʳ+zeʳ⇒singleton : ∀ {_•_ e} → RightIdentity e _•_ → RightZero e _•_ →
                    ∀ x y → x ≈ y
idʳ+zeʳ⇒singleton {_•_} {e} id ze x y = begin
  x     ≈⟨ sym (id x) ⟩
  x • e ≈⟨ ze x ⟩
  e     ≈⟨ sym (ze y) ⟩
  y • e ≈⟨ id y ⟩
  y     ∎

id+ze⇒singleton : ∀ {_•_ e} → Identity e _•_ → Zero e _•_ → ∀ x y → x ≈ y
id+ze⇒singleton {_•_} (id , _) (ze , _) = idˡ+zeˡ⇒singleton {_•_} id ze
