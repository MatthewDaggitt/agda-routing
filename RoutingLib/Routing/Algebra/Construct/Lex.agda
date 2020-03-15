--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module combines two routing algebras into a third composite routing
-- algebra via a lexicographic product. The routes are combined as pairs of the
-- old routes, with choice being implemented as the lexicographic product of the
-- two old choice operators, and extension being implemented pointwise using the
-- two old extension operators.
--
-- See RoutingLib.Protocols.ShortestWidestPaths for an example of how this may
-- be used.
--------------------------------------------------------------------------------

open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.Algebra.Construct.Lex
  {a₁ a₂ b₁ b₂ ℓ₁ ℓ₂}
  (algebraA : RawRoutingAlgebra a₁ b₁ ℓ₁)
  (algebraB : RawRoutingAlgebra a₂ b₂ ℓ₂)
  where

open import Algebra
open import Algebra.Consequences.Setoid
open import Data.Nat
open import Data.Fin
open import Data.Product
open import Data.Product.Relation.Binary.Pointwise.NonDependent
  as Pointwise using (Pointwise)
open import Data.Sum as Sum using ()
open import Level using (lift)
open import Relation.Binary
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation

open import RoutingLib.Algebra.Construct.Lexicographic
  as OpLex renaming (Lex to OpLex)
open import RoutingLib.Algebra.Construct.Lexicographic.Magma
  as OpLexProperties′
import RoutingLib.Routing.Algebra.Properties.RawRoutingAlgebra

private
  module A = RawRoutingAlgebra algebraA
  module B = RawRoutingAlgebra algebraB

  module LexProperties = OpLexProperties′ A.⊕-decMagma B.⊕-magma

------------------------------------------------------------------------
-- Algebra

infix 7 _⊕_
infix 6 _▷_
infix 4 _≈_

Route : Set _
Route = A.Route × B.Route

Step : ∀ {n} (i j : Fin n) → Set _
Step i j = A.Step i j × B.Step i j

_≈_ : Rel Route _
_≈_ = Pointwise A._≈_ B._≈_

_⊕_ : Op₂ Route
_⊕_ = OpLex A._≟_ A._⊕_ B._⊕_

_▷_ : ∀ {n} {i j : Fin n} → Step i j → Route → Route
(f , g) ▷ (a , b) = f A.▷ a , g B.▷ b

0# : Route
0# = A.0# , B.0#

∞# : Route
∞# = A.∞# , B.∞#

f∞ : ∀ {n} (i j : Fin n) → Step i j
f∞ i j = A.f∞ i j , B.f∞ i j

▷-cong : ∀ {n} {i j : Fin n} (f : Step i j) → Congruent₁ _≈_ (_▷_ f)
▷-cong (f , g) (a≈b , x≈y) = (A.▷-cong f a≈b) , B.▷-cong g x≈y

f∞-reject : ∀ {n} (i j : Fin n) x → (f∞ i j ▷ x) ≈ ∞#
f∞-reject i j (a , b) = A.f∞-reject i j a , B.f∞-reject i j b

Lex : RawRoutingAlgebra _ _ _
Lex = record
  { Route              = Route
  ; Step               = Step
  ; _≈_                = _≈_
  ; _⊕_                = _⊕_
  ; _▷_                = _▷_
  ; 0#                 = 0#
  ; ∞#                 = ∞#
  ; f∞                 = f∞
  ; ≈-isDecEquivalence = Pointwise.×-isDecEquivalence A.≈-isDecEquivalence B.≈-isDecEquivalence
  ; ⊕-cong             = LexProperties.cong
  ; ▷-cong             = ▷-cong
  ; f∞-reject          = f∞-reject
  }

open RawRoutingAlgebra Lex using (_≤₊_)

------------------------------------------------------------------------
-- IsRoutingAlgebra is preserved

isRoutingAlgebra : IsRoutingAlgebra algebraA →
                   IsRoutingAlgebra algebraB →
                   IsRoutingAlgebra Lex
isRoutingAlgebra A-isRA B-isRA = record
  { ⊕-sel         = LexProperties.sel       Aᵣ.⊕-sel       Bᵣ.⊕-sel
  ; ⊕-comm        = LexProperties.comm      Aᵣ.⊕-comm      Bᵣ.⊕-comm
  ; ⊕-assoc       = LexProperties.assoc     Aᵣ.⊕-assoc     Bᵣ.⊕-assoc Aᵣ.⊕-sel Aᵣ.⊕-comm
  ; ⊕-zeroʳ       = LexProperties.zeroʳ     Aᵣ.⊕-zeroʳ     Bᵣ.⊕-zeroʳ
  ; ⊕-identityʳ   = LexProperties.identityʳ Aᵣ.⊕-identityʳ Bᵣ.⊕-identityʳ
  ; ▷-fixedPoint  = λ {(f , g) → Aᵣ.▷-fixedPoint f , Bᵣ.▷-fixedPoint g}
  } where
  module Aᵣ = IsRoutingAlgebra A-isRA
  module Bᵣ = IsRoutingAlgebra B-isRA

------------------------------------------------------------------------
-- Other properties

module _ (⊕ᴬ-comm : Commutative A._≈_ A._⊕_) (⊕ᴬ-sel : Selective A._≈_ A._⊕_) where

  distrib-bump :  ∀ {k ⊥ᴮ ⊤ᴮ} →
                  IsLevel_DistributiveAlt algebraA 1 →
                  Level_DistributiveIn[_,_]Alt algebraB k ⊥ᴮ ⊤ᴮ →
                  Level_DistributiveIn[_,_]Alt Lex (suc k) (A.0# , ⊥ᴮ) (A.∞# , ⊤ᴮ)
  distrib-bump {zero}  eq (lift 0ᴮ≈∞ᴮ)        (f , g) {x , a} {y , b} ⊥≤x x≤⊤ ⊥≤y y≤⊤ = Level.lift ({!!} , {!!})
  distrib-bump {suc k} A-distrib    B-distrib (f , g) {x , a} {y , b} ⊥≤x x≤⊤ ⊥≤y y≤⊤ =
    rec
    -- distrib-bump ? {!B-distrib g ? ? ? ?!}
    where
    rec : Level_DistributiveIn[_,_]Alt Lex (suc k) ((f , g) ▷ (x , a) ⊕ (y , b)) (((f , g) ▷ (x , a)) ⊕ ((f , g) ▷ (y , b)))
    rec = {!isLevelDistrib-cong ? ? ?!}
    
    recA : Level_DistributiveIn[_,_]Alt algebraA k (f A.▷ x A.⊕ y) ((f A.▷ x) A.⊕ (f A.▷ y))
    recA = {!!}

    recB : {!!}
    recB = {!!}

{-


distrib-1st-comp : Selective A._≈_ A._⊕_ → 
                   IsDistributive algebraA →
                   ∀ {n} {i j : Fin n} (f : Step i j) {x y} →
                   proj₁ (f ▷ (x ⊕ y)) A.≈ proj₁ ((f ▷ x) ⊕ (f ▷ y)) 
distrib-1st-comp A-sel A-distrib (f , g) {(a , x)} {(b , y)}
  with a A.⊕ b A.≟ a | a A.⊕ b A.≟ b
    | (f A.▷ a) A.⊕ (f A.▷ b) A.≟ f A.▷ a | (f A.▷ a) A.⊕ (f A.▷ b) A.≟ f A.▷ b
... | yes p | yes p₁ | yes p₂ | yes p₃ = A-distrib f a b
... | yes p | no ¬p | yes p₁ | yes p₂ = A.≈-sym p₁
... | yes p | no ¬p | yes p₁ | no ¬p₁ = A.≈-refl
... | yes a⊕b≈a | _ | no fa⊕fb≉fa | _ = contradiction (A.≈-trans (A.≈-sym (A-distrib f a b)) (A.▷-cong f a⊕b≈a)) fa⊕fb≉fa
... | _ | yes a⊕b≈b | _ | no fa⊕fb≉fb = contradiction (A.≈-trans (A.≈-sym (A-distrib f a b)) (A.▷-cong f a⊕b≈b)) fa⊕fb≉fb
... | no ¬p | yes p | yes p₁ | yes p₂ = A.≈-sym p₂
... | no ¬p | yes p | no ¬p₁ | yes p₁ = A.≈-refl
... | no a⊕b≉a | no a⊕b≉b | _ | _  = Sum.[ contradiction ◌ a⊕b≉a , contradiction ◌ a⊕b≉b ] (A-sel a b)

middle-1st-comp : Idempotent A._≈_ A._⊕_ →
                  Commutative A._≈_ A._⊕_ →
                  ∀ {x y z} → x ≤₊ y → y ≤₊ z →
                  proj₁ x A.≈ proj₁ z → proj₁ x A.≈ proj₁ y
middle-1st-comp A-idem A-comm {a , x} {b , y} {c , z} ax≤by by≤cz a≈c
  with c A.⊕ b A.≟ c | c A.⊕ b A.≟ b | b A.⊕ a A.≟ b | b A.⊕ a A.≟ a
... | yes p | yes p₁ | _      | _      = A.≈-trans (A.≈-trans a≈c (A.≈-sym p)) p₁
... | _     | _      | yes p₁ | yes p₂ = A.≈-trans (A.≈-sym p₂) p₁ 
... | yes p | no ¬p  | _      | _      = contradiction (A.≈-trans (A.⊕-cong (proj₁ by≤cz) A.≈-refl) (A-idem b)) ¬p
... | _     | _      | no ¬p₁ | no ¬p₂ = contradiction (proj₁ ax≤by) ¬p₂
... | _     | _      | yes _  | no _   = A.≈-sym (proj₁ ax≤by)
... | no c⊕b≉c | yes c⊕b≈b  | no b⊕a≉b | yes b⊕a≈a = contradiction (A.≈-trans (A.≈-trans (A-comm b a) (A.⊕-cong a≈c A.≈-refl)) c⊕b≈b) b⊕a≉b
... | no ¬p | no ¬p₁ | _      | _      = contradiction (proj₁ by≤cz) ¬p₁

bumpDistributivity : Commutative A._≈_ A._⊕_ →
                     Selective A._≈_ A._⊕_ →
                     IsDistributive algebraA →
                     IsDistributive algebraB →
                     IsLevel_Distributive Lex 1
bumpDistributivity A-comm A-sel A-distrib B-distrib
  f {p@(a , w)} {q@(b , x)} _ _ _ _ (k , l) {r@(c , y)} {s@(d , z)}
  f[p⊕q]≤r r≤fp⊕fq f[p⊕q]≤s s≤fp⊕fq with sel⇒idem A.S A-sel
... | A-idem with middle-1st-comp A-idem A-comm f[p⊕q]≤r r≤fp⊕fq (distrib-1st-comp A-sel A-distrib f)
                | middle-1st-comp A-idem A-comm f[p⊕q]≤s s≤fp⊕fq (distrib-1st-comp A-sel A-distrib f)
...   | f[p⊕q]₁≈c | f[p⊕q]₁≈d with A.≈-trans (A.≈-sym f[p⊕q]₁≈c) f[p⊕q]₁≈d
...     | c≈d with c A.⊕ d A.≟ c | c A.⊕ d A.≟ d | (k A.▷ c) A.⊕ (k A.▷ d) A.≟ k A.▷ c | (k A.▷ c) A.⊕ (k A.▷ d) A.≟ k A.▷ d
...       | yes p     | yes p₁    | yes p₂ | yes p₃ =
  A-distrib k c d , B-distrib l y z
...       | yes c⊕d≈c | yes c⊕d≈d | yes kc⊕kd≈kc | no kc⊕kd≉kd =
  contradiction (A.≈-trans kc⊕kd≈kc (A.▷-cong k (A.≈-trans (A.≈-sym c⊕d≈c) c⊕d≈d))) kc⊕kd≉kd
...       | yes c⊕d≈c | yes c⊕d≈d | no kc⊕kd≉kc | yes kc⊕kd≈kd =
  contradiction (A.≈-trans kc⊕kd≈kd (A.▷-cong k (A.≈-trans (A.≈-sym c⊕d≈d) c⊕d≈c))) kc⊕kd≉kc
...       | yes p     | yes p₁    | no ¬p | no ¬p₁ =
  A-distrib k c d , B-distrib l y z
...       | _         | no c⊕d≉d | _ | _ =
  contradiction (A.≈-trans (A.⊕-cong c≈d A.≈-refl) (A-idem d)) c⊕d≉d
...       | no c⊕d≉c  | _ | _ | _ =
  contradiction (A.≈-trans (A.⊕-cong A.≈-refl (A.≈-sym c≈d)) (A-idem c)) c⊕d≉c


bumpDistributivity2 : Commutative A._≈_ A._⊕_ →
                     Selective A._≈_ A._⊕_ →
                     ∀ {k} →
                     IsLevel_DistributiveAlt algebraA k →
                     IsLevel_DistributiveAlt algebraA k →
                     IsLevel_DistributiveAlt Lex (suc k)
bumpDistributivity2 A-comm A-sel {zero} (lift 0≈ᵃ∞) (lift 0≈ᵇ∞) f {a , w} {b , x} _ _ _ _
  (m , l) {r@(c , y)} {s@(d , z)} f[p⊕q]≤r r≤fp⊕fq f[p⊕q]≤s s≤fp⊕fq = {!!} , {!!}
bumpDistributivity2 A-comm A-sel {suc k} A-distrib B-distrib f {a , w} {b , x} _ _ _ _
  (m , l) {r@(c , y)} {s@(d , z)} f[p⊕q]≤r r≤fp⊕fq f[p⊕q]≤s s≤fp⊕fq with sel⇒idem A.S A-sel
... | A-idem with c A.⊕ d A.≟ c | c A.⊕ d A.≟ d | (k A.▷ c) A.⊕ (k A.▷ d) A.≟ k A.▷ c | (k A.▷ c) A.⊕ (k A.▷ d) A.≟ k A.▷ d
...       | yes p     | yes p₁    | yes p₂ | yes p₃ =
  A-distrib k c d , B-distrib l y z
...       | yes c⊕d≈c | yes c⊕d≈d | yes kc⊕kd≈kc | no kc⊕kd≉kd =
  contradiction (A.≈-trans kc⊕kd≈kc (A.▷-cong k (A.≈-trans (A.≈-sym c⊕d≈c) c⊕d≈d))) kc⊕kd≉kd
...       | yes c⊕d≈c | yes c⊕d≈d | no kc⊕kd≉kc | yes kc⊕kd≈kd =
  contradiction (A.≈-trans kc⊕kd≈kd (A.▷-cong k (A.≈-trans (A.≈-sym c⊕d≈d) c⊕d≈c))) kc⊕kd≉kc
...       | yes p     | yes p₁    | no ¬p | no ¬p₁ =
  A-distrib k c d , B-distrib l y z
...       | _         | no c⊕d≉d | _ | _ = ?
  -- contradiction (A.≈-trans (A.⊕-cong c≈d A.≈-refl) (A-idem d)) c⊕d≉d
...       | no c⊕d≉c  | _ | _ | _ = ?
  -- contradiction (A.≈-trans (A.⊕-cong A.≈-refl (A.≈-sym c≈d)) (A-idem c)) c⊕d≉c

-}

{-
with middle-1st-comp A-idem A-comm f[p⊕q]≤r r≤fp⊕fq (distrib-1st-comp A-sel A-distrib f)
                | middle-1st-comp A-idem A-comm f[p⊕q]≤s s≤fp⊕fq (distrib-1st-comp A-sel A-distrib f)
...   | f[p⊕q]₁≈c | f[p⊕q]₁≈d = ?
with A.≈-trans (A.≈-sym f[p⊕q]₁≈c) f[p⊕q]₁≈d
...     | c≈d 
-}
