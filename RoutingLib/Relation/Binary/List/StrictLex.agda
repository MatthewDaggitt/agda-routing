open import Level using () renaming (zero to lzero)
open import Data.List using (_∷_; [])
open import Relation.Binary
open import Relation.Binary.List.Pointwise  as Pointwise using ([]; _∷_) renaming (Rel to ListRel)
open import Relation.Binary.List.NonStrictLex using (Lex-≤; Lex; ≤-isPreorder)
open import Relation.Binary.List.StrictLex using (base; this; halt; next)

module RoutingLib.Relation.Binary.List.StrictLex {A : Set} where

{-

  antisymmetric :
    ∀ {P} {_≈_ _<_ : Rel A lzero} →
    Symmetric _≈_ → Antisymmetric _≈_ _<_ →
    Antisymmetric (ListRel _≈_) (Lex P _≈_ _<_)
  antisymmetric {P} {_≈_} {_<_} sym antisym = as
    where
    as : Antisymmetric (ListRel _≈_) (Lex P _≈_ _<_)
    as (base _)         (base _)         = []
    as halt             ()
    as (this x<y)       (this y<x)       = ?
    as (this x<y)       (next y≈x ys⊴xs) = (sym y≈x) ∷ {!!}
    as (next x≈y xs⊴ys) (this y<x)       = x≈y ∷ {!!}
    as (next x≈y xs⊴ys) (next y≈x ys⊴xs) = x≈y ∷ as xs⊴ys ys⊴xs


  ≤-isPartialOrder : ∀ {_≈_ _<_ : Rel A lzero} →
                     IsPartialOrder _≈_ _<_ →
                     IsPartialOrder (ListRel _≈_) (Lex-≤ _≈_ _<_)
  ≤-isPartialOrder {_≈_} {_<_} po = record { 
      isPreorder = ≤-isPreorder isEquivalence {!!} {!!}; 
      antisym    = antisymmetric {!!}  {!!}
                     --(trans∧irr⟶asym {_≈_ = _≈_} {_<_ = _<_} Eq.refl trans irrefl)
    }
    where open IsPartialOrder po

-}
{-
  ≤-isDecTotalOrder : ∀ {_≈_ _<_} →
                      IsDecTotalOrder _≈_ _<_ →
                      IsDecTotalOrder (Pointwise.Rel _≈_) (Lex-≤ _≈_ _<_)
  ≤-isDecTotalOrder sto = record
    { isTotalOrder = ≤-isTotalOrder ?
    ; _≟_          = Pointwise.decidable _≟_
    ; _≤?_         = ≤-decidable _≟_ (tri⟶dec< compare)
    } where open IsStrictTotalOrder sto
-}
