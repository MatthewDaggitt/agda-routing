
open import Level
open import Data.Product using (_×_)

module RoutingLib.Relation.Nullary where

private
  variable
    a b : Level
    
_⇔_ : Set a → Set b → Set _
A ⇔ B = (A → B) × (B → A)
