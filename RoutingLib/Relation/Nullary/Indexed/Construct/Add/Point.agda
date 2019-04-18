module RoutingLib.Relation.Nullary.Indexed.Construct.Add.Point
  {i} {I : Set i} where

open import Data.Unit using (tt)
open import Function using (_∘_)
open import Level
open import Relation.Unary using (Pred)

open import Data.Maybe public
  using (Maybe)
  renaming
  ( nothing    to ∙ᵢ
  ; just       to [_]ᵢ
  ; Is-just    to IsValueᵢ
  ; to-witness to extractValueᵢ
  )

open import Data.Maybe.Relation.Unary.Any public
  renaming (just to [_]ᵢ)

Pointedᵢ : ∀ {a} (A : I → Set a) → (I → Set a)
Pointedᵢ A i = Maybe (A i)

module _ {a} {Aᵢ : I → Set a} where

  private
    A : Set (i ⊔ a)
    A = ∀ i → Aᵢ i

    A∙ : Set (i ⊔ a)
    A∙ = ∀ i → Pointedᵢ Aᵢ i

  ∙ : A∙
  ∙ i = ∙ᵢ

  [_] : A → A∙
  [ x ] i = [ x i ]ᵢ

  IsValue : Pred A∙ (i ⊔ a)
  IsValue x = ∀ i → IsValueᵢ (x i)

  extractValue : ∀ {x} → IsValue x → A
  extractValue = extractValueᵢ ∘_

  IsValue[_] : ∀ x → IsValue [ x ]
  IsValue[_] x i = [ tt ]ᵢ
