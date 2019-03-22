
open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.Algebra.Construct.AddIdentity
  {a b ℓ} (A : RawRoutingAlgebra a b ℓ) where

open RawRoutingAlgebra A

open import Algebra.FunctionProperties
open import Data.Fin using (Fin; toℕ)
open import Relation.Binary
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Algebra.Construct.Add.Identity 
open import RoutingLib.Relation.Nullary.Construct.Add.Point renaming (∙ to identity ) 
open import RoutingLib.Relation.Binary.Construct.Add.Point.Equality 

infix 4 _≈ⁱ_
infix 7 _⊕ⁱ_
infix 6 _▷ⁱ_

Routeⁱ : Set a
Routeⁱ = Pointed Route 

_≈ⁱ_ : Rel Routeⁱ ℓ
_≈ⁱ_ = _≈∙_ _≈_

≈ⁱ-refl : Reflexive _≈ⁱ_
≈ⁱ-refl = ≈∙-refl _≈_ ≈-refl

≈ⁱ-sym : Symmetric _≈ⁱ_
≈ⁱ-sym = ≈∙-sym _≈_ ≈-sym

≈ⁱ-trans : Transitive _≈ⁱ_
≈ⁱ-trans = ≈∙-trans _≈_ ≈-trans 

_⊕ⁱ_ : Op₂ Routeⁱ
_⊕ⁱ_ = _⊕∙_ _⊕_   

_▷ⁱ_ : ∀ {n} {i j : Fin n} → Step i j → Routeⁱ → Routeⁱ
_▷ⁱ_ {_} {i} {j} f identity    = identity
_▷ⁱ_ {_} {i} {j} f [ x ] with (f ▷ x) ≟ ∞#
... | yes _ = identity
... | no _  = [ f ▷ x ] 

0#ⁱ : Routeⁱ
0#ⁱ = [ 0# ] 

∞#ⁱ : Routeⁱ
∞#ⁱ = identity

f∞ⁱ : ∀ {n} (i j : Fin n) → Step i j
f∞ⁱ = f∞

≈ⁱ-isEquivalence : IsEquivalence _≈ⁱ_
≈ⁱ-isEquivalence =  ≈∙-isEquivalence _≈_ ≈-isEquivalence   

≈ⁱ-isDecEquivalence : IsDecEquivalence _≈ⁱ_
≈ⁱ-isDecEquivalence =  ≈∙-isDecEquivalence _≈_ ≈-isDecEquivalence

_≟ⁱ_ : Decidable _≈ⁱ_
_≟ⁱ_ = ≈∙-dec _ _≟_ -- 

⊕ⁱ-cong : Congruent₂ _≈ⁱ_ _⊕ⁱ_
⊕ⁱ-cong = ⊕∙-cong _ ≈-refl ⊕-cong 


-- TGG : how to prove this simple fact? 
postulate []≉identity : ∀ x → ¬([ x ] ≈ⁱ identity) 

▷ⁱ-cong : ∀ {n} {i j : Fin n} (f : Step i j) → Congruent₁ _≈ⁱ_ (f ▷ⁱ_)
▷ⁱ-cong {_} {i} {j} f {identity} {identity} ∙≈∙  = ∙≈∙
▷ⁱ-cong {_} {i} {j} f {[ x ]}    {identity} x≈y  = contradiction x≈y ([]≉identity x)
▷ⁱ-cong {_} {i} {j} f {identity} {[ y ]} x≈y     = contradiction (≈ⁱ-sym x≈y) ([]≉identity y)
▷ⁱ-cong {_} {i} {j} f {[ x ]} {[ y ]} x≈y with (f ▷ x) ≟ ∞# | (f ▷ y) ≟ ∞#
...| yes p | yes p₁ = ∙≈∙
...| yes p | no ¬p = contradiction (≈-trans (▷-cong f (≈-sym ([≈]-injective _ x≈y))) p) ¬p  
...| no ¬p | yes p = contradiction (≈-trans (▷-cong f ([≈]-injective _ x≈y)) p) ¬p 
...| no ¬p | no ¬p₁ = [ (▷-cong f ([≈]-injective _ x≈y)) ] 

f∞ⁱ-reject : ∀ {n} (i j : Fin n) (x : Routeⁱ) → f∞ⁱ i j ▷ⁱ x ≈ⁱ ∞#ⁱ
f∞ⁱ-reject i j identity         = ∙≈∙
f∞ⁱ-reject i j ([ x ]) with  f∞ i j ▷ x ≟ ∞#
... | yes f∞▷x≈∞      = ∙≈∙  -- 
... | no  f∞▷x≉∞ = contradiction (f∞-reject i j x) f∞▷x≉∞

Add-Identity : RawRoutingAlgebra a b ℓ
Add-Identity = record
    { Route              = Routeⁱ
    ; Step               = Step
    ; _≈_                = _≈ⁱ_
    ; _⊕_                = _⊕ⁱ_
    ; _▷_                = _▷ⁱ_
    ; 0#                 = 0#ⁱ
    ; ∞#                 = ∞#ⁱ
    ; f∞                 = f∞ⁱ
    ; ≈-isDecEquivalence = ≈ⁱ-isDecEquivalence 
    ; ⊕-cong             = ⊕ⁱ-cong
    ; ▷-cong             = ▷ⁱ-cong
    ; f∞-reject          = f∞ⁱ-reject
    }


⊕ⁱ-sel : Selective _≈_ _⊕_ → Selective _≈ⁱ_ _⊕ⁱ_
⊕ⁱ-sel ⊕-sel = ⊕∙-sel _ ≈-refl ⊕-sel 

⊕ⁱ-comm : Commutative _≈_ _⊕_ → Commutative _≈ⁱ_ _⊕ⁱ_
⊕ⁱ-comm ⊕-comm =  ⊕∙-comm _ ≈-refl ⊕-comm 

⊕ⁱ-assoc : Associative _≈_ _⊕_ → Associative _≈ⁱ_ _⊕ⁱ_
⊕ⁱ-assoc ⊕-assoc = ⊕∙-assoc _ ≈-refl ⊕-assoc

⊕ⁱ-zeroʳ : RightZero _≈_ 0# _⊕_ → RightZero _≈ⁱ_ 0#ⁱ _⊕ⁱ_
⊕ⁱ-zeroʳ ⊕-zeroʳ = ⊕∙-zeroʳ _ ≈-refl ⊕-zeroʳ 

⊕ⁱ-identityʳ : RightIdentity _≈ⁱ_ ∞#ⁱ _⊕ⁱ_
⊕ⁱ-identityʳ = ⊕∙-identityʳ _ ≈-refl

▷ⁱ-fixedPoint : ∀ {n} {i j : Fin n} (f : Step i j) → f ▷ⁱ ∞#ⁱ ≈ⁱ ∞#ⁱ
▷ⁱ-fixedPoint f = ∙≈∙

isRoutingAlgebra : IsRoutingAlgebra A → IsRoutingAlgebra Add-Identity
isRoutingAlgebra A-isRoutingAlgebra = record
    { ⊕-sel        = ⊕ⁱ-sel ⊕-sel
    ; ⊕-comm       = ⊕ⁱ-comm ⊕-comm
    ; ⊕-assoc      = ⊕ⁱ-assoc ⊕-assoc
    ; ⊕-zeroʳ       = ⊕ⁱ-zeroʳ ⊕-zeroʳ 
    ; ⊕-identityʳ   = ⊕ⁱ-identityʳ
    ; ▷-fixedPoint = ▷ⁱ-fixedPoint
    }
    where open IsRoutingAlgebra A-isRoutingAlgebra 




