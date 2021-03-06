

module RoutingLib.Algebra.Definitions {a} {A : Set a} where

open import Algebra.Core using (Op₂)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (Level; _⊔_)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Tri; Rel; _Preserves₂_⟶_⟶_; _Preserves_⟶_)

private
  variable
    p : Level
    P : Pred A p
    
_Preservesˡ_ : Op₂ A → Pred A p → Set _
_•_ Preservesˡ P = ∀ {a} b → P a → P (a • b)

_Preservesʳ_ : Op₂ A → Pred A p → Set _
_•_ Preservesʳ P = ∀ a {b} → P b → P (a • b)

_Preservesᵒ_ : Op₂ A → Pred A p → Set _
_•_ Preservesᵒ P = ∀ a b → P a ⊎ P b → P (a • b)

_Preservesᵇ_ : Op₂ A → Pred A p → Set _
_•_ Preservesᵇ P = ∀ {a b} → P a → P b → P (a • b)


_Forcesˡ_ : Op₂ A → Pred A p → Set _
_•_ Forcesˡ P = ∀ a b → P (a • b) → P a

_Forcesʳ_ : Op₂ A → Pred A p → Set _
_•_ Forcesʳ P = ∀ a b → P (a • b) → P b

_Forcesᵇ_ : Op₂ A → Pred A p → Set _
_•_ Forcesᵇ P = ∀ a b → P (a • b) → P a × P b

_Forcesᵒ_ : Op₂ A → Pred A p → Set _
_•_ Forcesᵒ P = ∀ a b → P (a • b) → P a ⊎ P b



------------------------------------------------------------------------------
-- Properties

presᵒ⇒presˡ : ∀ {_•_} → _•_ Preservesᵒ P → _•_ Preservesˡ P
presᵒ⇒presˡ pres b Pa = pres _ b (inj₁ Pa)

presᵒ⇒presʳ : ∀ {_•_} → _•_ Preservesᵒ P → _•_ Preservesʳ P
presᵒ⇒presʳ pres a Pb = pres a _ (inj₂ Pb)

forcesᵇ⇒forcesˡ : ∀ {_•_} → _•_ Forcesᵇ P → _•_ Forcesˡ P
forcesᵇ⇒forcesˡ forces a b P = proj₁ (forces a b P)

forcesᵇ⇒forcesʳ : ∀ {_•_} → _•_ Forcesᵇ P → _•_ Forcesʳ P
forcesᵇ⇒forcesʳ forces a b P = proj₂ (forces a b P)
