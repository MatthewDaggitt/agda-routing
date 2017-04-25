open import Level using (_⊔_) renaming (zero to lzero)
open import Data.Nat using (ℕ; suc) renaming (_≤_ to _≤ℕ_)
open import Relation.Nullary using (¬_; yes; no)
open import Data.Product using (_×_; _,_)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Maybe using (just; nothing)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; subst) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Algebra.FunctionProperties using (Op₂; Congruent₂; Selective)

open import RoutingLib.Algebra.FunctionProperties using (_Preservesₗ_)
open import RoutingLib.Routing.Definitions
open import RoutingLib.Data.Graph using (Graph; _∈?_)
open import RoutingLib.Data.Graph.SimplePath renaming (_≈_ to _≈ₚ_)
open import RoutingLib.Data.Graph.SimplePath.Properties using (_≤ₚ?_; _∉?_; ≤ₚ-resp-≈; ∉-resp-≈; p≈q⇒p₀≡q₀) renaming (_≟_ to _≟ₚ_; ≈-refl to ≈ₚ-refl; ≈-sym to ≈ₚ-sym; ≈-trans to ≈ₚ-trans)
open import RoutingLib.Relation.Binary.RespectedBy using (_RespectedBy_; Respects₂⇨RespectedBy)


module RoutingLib.Routing.AlgebraicPaths.Inconsistent
  {a b ℓ} (ra : RoutingAlgebra a b ℓ)
  (⊕-sel : Selective (RoutingAlgebra._≈_ ra) (RoutingAlgebra._⊕_ ra))
  {n : ℕ}
  (G : Graph (RoutingAlgebra.Step ra) n)
  where

  -----------
  -- Setup --
  -----------

  open RoutingAlgebra ra

  open import RoutingLib.Algebra.Selectivity.Properties _≈_ _⊕_ ⊕-sel using (selection; SelCase)
  open import RoutingLib.Algebra.Selectivity.Properties _≈_ _⊕_ ⊕-sel using (sel₁; sel₂; sel≈) public

  select : ∀ x y → SelCase x y
  select = selection sym trans _≟_


  --------------------------------
  -- Consistent routing algebra --
  --------------------------------

  -- Routes are formed by the product R × EPath along with a zero added (the null path)

  data IRoute : Set (a ⊔ b ⊔ ℓ) where
    inull  : IRoute
    iroute : Route → SimplePath n → IRoute


  -- Steps

  IStep : Set lzero
  IStep = Fin n × Fin n


  -- Choice operator

  infix 7 _⊕ⁱ_

  _⊕ⁱ_ : Op₂ IRoute
  inull ⊕ⁱ r     = r
  r     ⊕ⁱ inull = r
  (iroute x p) ⊕ⁱ (iroute y q) with select x y
  ... | sel₁ _ _ = iroute x p
  ... | sel₂ _ _ = iroute y q
  ... | sel≈ _ _ with p ≤ₚ? q
  ...   | yes _ = iroute x p
  ...   | no  _ = iroute y q



  -- Extension operator

  infix 6 _▷ⁱ_

  _▷ⁱ_ : IStep → IRoute → IRoute
  _       ▷ⁱ inull = inull
  (i , j) ▷ⁱ (iroute x []) with i ≟ᶠ j | (i , j) ∈? G
  ... | yes _  | _           = inull
  ... | _      | no  _       = inull
  ... | no i≢j | yes (v , _) with v ▷ x ≟ 0#
  ...   | yes _ = inull
  ...   | no  _ = iroute (v ▷ x) [ i ∺ j ∣ i≢j ]
  (i , j) ▷ⁱ (iroute x [ p ]) with j ≟ᶠ source p | i ∉? [ p ] | (i , j) ∈? G
  ... | no _       | _       | _           = inull
  ... | _          | no  _   | _           = inull
  ... | _          | _       | no _        = inull
  ... | yes j≡s[p] | yes [ i∉p ] | yes (v , _) with v ▷ x ≟ 0#
  ...   | yes _ = inull
  ...   | no  _ = iroute (v ▷ x) [ i ∷ p ∣ i∉p ]



  -- Equality

  infix 4 _≈ⁱ_ _≉ⁱ_

  data _≈ⁱ_ : Rel IRoute (a ⊔ b ⊔ ℓ) where
    inullEq  : inull ≈ⁱ inull
    irouteEq : ∀ {x y p q} → x ≈ y → p ≈ₚ q → iroute x p ≈ⁱ iroute y q

  _≉ⁱ_ : Rel IRoute (a ⊔ b ⊔ ℓ)
  x ≉ⁱ y = ¬ (x ≈ⁱ y)

  abstract

    -- equality is a decidable equivalence

    ≈ⁱ-refl : Reflexive _≈ⁱ_
    ≈ⁱ-refl {inull} = inullEq
    ≈ⁱ-refl {iroute _ _} = irouteEq refl ≈ₚ-refl

    ≈ⁱ-reflexive : _≡_ ⇒ _≈ⁱ_
    ≈ⁱ-reflexive ≡-refl = ≈ⁱ-refl

    ≈ⁱ-sym : Symmetric _≈ⁱ_
    ≈ⁱ-sym inullEq            = inullEq
    ≈ⁱ-sym (irouteEq x≈y p≈q) = irouteEq (sym x≈y) (≈ₚ-sym p≈q)

    ≈ⁱ-trans : Transitive _≈ⁱ_
    ≈ⁱ-trans inullEq inullEq = inullEq
    ≈ⁱ-trans (irouteEq x≈y p≈q) (irouteEq y≈z q≈r) = irouteEq (trans x≈y y≈z) (≈ₚ-trans p≈q q≈r)

    _≟ⁱ_ : Decidable _≈ⁱ_
    inull ≟ⁱ inull = yes inullEq
    inull ≟ⁱ (iroute _ _) = no λ()
    (iroute _ _) ≟ⁱ inull = no λ()
    (iroute x p) ≟ⁱ (iroute y q) with x ≟ y | p ≟ₚ q
    ... | no  x≉y | _       = no λ{(irouteEq x≈y _) → x≉y x≈y}
    ... | _       | no  p≉q = no λ{(irouteEq _ p≈q) → p≉q p≈q}
    ... | yes x≈y | yes p≈q = yes (irouteEq x≈y p≈q)

    ⊕ⁱ-pres-≈ⁱ : Congruent₂ _≈ⁱ_ _⊕ⁱ_
    ⊕ⁱ-pres-≈ⁱ inullEq inullEq = inullEq
    ⊕ⁱ-pres-≈ⁱ inullEq (irouteEq y≈z r≈s) = irouteEq y≈z r≈s
    ⊕ⁱ-pres-≈ⁱ (irouteEq w≈x p≈q) inullEq = irouteEq w≈x p≈q
    ⊕ⁱ-pres-≈ⁱ {iroute w p} {iroute x q} {iroute y r} {iroute z s} (irouteEq w≈x p≈q) (irouteEq y≈z r≈s) with select w y | select x z
    ... | sel₁ _     _     | sel₁ _     _     = irouteEq w≈x p≈q
    ... | sel₁ _     w⊕y≉y | sel₂ _     x⊕z≈z = contradiction (trans (trans (⊕-pres-≈ w≈x y≈z) x⊕z≈z) (sym y≈z)) w⊕y≉y
    ... | sel₁ _     w⊕y≉y | sel≈ _     x⊕z≈z = contradiction (trans (trans (⊕-pres-≈ w≈x y≈z) x⊕z≈z) (sym y≈z)) w⊕y≉y
    ... | sel₂ w⊕y≉w _     | sel₁ x⊕z≈x _     = contradiction (trans (trans (⊕-pres-≈ w≈x y≈z) x⊕z≈x) (sym w≈x)) w⊕y≉w
    ... | sel₂ _     _     | sel₂ _     _     = irouteEq y≈z r≈s
    ... | sel₂ w⊕y≉w _     | sel≈ x⊕z≈x _     = contradiction (trans (trans (⊕-pres-≈ w≈x y≈z) x⊕z≈x) (sym w≈x)) w⊕y≉w
    ... | sel≈ _     w⊕y≈y | sel₁ _     x⊕z≉z = contradiction (trans (trans (sym (⊕-pres-≈ w≈x y≈z)) w⊕y≈y) y≈z) x⊕z≉z
    ... | sel≈ w⊕y≈w _     | sel₂ x⊕z≉x _     = contradiction (trans (trans (sym (⊕-pres-≈ w≈x y≈z)) w⊕y≈w) w≈x) x⊕z≉x
    ... | sel≈ _     _     | sel≈ _     _     with p ≤ₚ? r | q ≤ₚ? s
    ...   | yes _   | yes _   = irouteEq w≈x p≈q
    ...   | yes p≤r | no  q≰s = contradiction (≤ₚ-resp-≈ p≈q r≈s p≤r) q≰s
    ...   | no  p≰r | yes q≤s = contradiction (≤ₚ-resp-≈ (≈ₚ-sym p≈q) (≈ₚ-sym r≈s) q≤s) p≰r
    ...   | no  _   | no  _   = irouteEq y≈z r≈s

    ▷ⁱ-pres-≈ⁱ : _▷ⁱ_ Preservesₗ _≈ⁱ_
    ▷ⁱ-pres-≈ⁱ (_ , _) inullEq = inullEq
    ▷ⁱ-pres-≈ⁱ (i , j) {iroute x []}    {iroute y []}    (irouteEq x≈y []) with i ≟ᶠ j | (i , j) ∈? G
    ... | yes _ | _           = inullEq
    ... | no  _ | no  _       = inullEq
    ... | no  _ | yes (v , _) with v ▷ x ≟ 0# | v ▷ y ≟ 0#
    ...   | yes _     | yes _     = inullEq
    ...   | yes v▷x≈0 | no  v▷y≉0 = contradiction (trans (▷-pres-≈ v (sym x≈y)) v▷x≈0) v▷y≉0
    ...   | no  v▷x≉0 | yes v▷y≈0 = contradiction (trans (▷-pres-≈ v x≈y) v▷y≈0) v▷x≉0
    ...   | no  _     | no _      = irouteEq (▷-pres-≈ v x≈y) ≈ₚ-refl
    ▷ⁱ-pres-≈ⁱ (i , j) {iroute x [ _ ]} {iroute y []}    (irouteEq x≈y ())
    ▷ⁱ-pres-≈ⁱ (i , j) {iroute x [ p ]} {iroute y [ q ]} (irouteEq x≈y [ p≈q ]) with j ≟ᶠ source p | j ≟ᶠ source q | i ∉? [ p ] | i ∉? [ q ] | (i , j) ∈? G
    ... | no  _    | no  _    | _       | _       | _           = inullEq
    ... | no  j≢p₀ | yes j≡q₀ | _       | _       | _           = contradiction (≡-trans j≡q₀ (≡-sym (p≈q⇒p₀≡q₀ p≈q))) j≢p₀
    ... | yes j≡p₀ | no  j≢q₀ | _       | _       | _           = contradiction (≡-trans j≡p₀ (p≈q⇒p₀≡q₀ p≈q)) j≢q₀
    ... | yes _    | yes _    | no  _   | no  _   | _           = inullEq
    ... | yes _    | yes _    | no  i∈p | yes i∉q | _           = contradiction (∉-resp-≈ (≈ₚ-sym [ p≈q ]) i∉q) i∈p
    ... | yes _    | yes _    | yes i∉p | no  i∈q | _           = contradiction (∉-resp-≈ [ p≈q ] i∉p ) i∈q
    ... | yes _    | yes _    | yes _   | yes  _  | no  _       = inullEq
    ... | yes _    | yes _    | yes [ _ ] | yes [ _ ] | yes (v , _) with v ▷ x ≟ 0# | v ▷ y ≟ 0#
    ...   | yes _     | yes _     = inullEq
    ...   | yes v▷x≈0 | no  v▷y≉0 = contradiction (trans (▷-pres-≈ v (sym x≈y)) v▷x≈0) v▷y≉0
    ...   | no  v▷x≉0 | yes v▷y≈0 = contradiction (trans (▷-pres-≈ v x≈y) v▷y≈0) v▷x≉0
    ...   | no  _     | no _      = irouteEq (▷-pres-≈ v x≈y) [ ≡-refl ∷ p≈q ]

    ≈ⁱ-isEquivalence : IsEquivalence _≈ⁱ_
    ≈ⁱ-isEquivalence = record 
      { refl  = ≈ⁱ-refl 
      ; sym   = ≈ⁱ-sym 
      ; trans = ≈ⁱ-trans
      }

    ≈ⁱ-isDecEquivalence : IsDecEquivalence _≈ⁱ_
    ≈ⁱ-isDecEquivalence = record 
      { isEquivalence = ≈ⁱ-isEquivalence 
      ; _≟_           = _≟ⁱ_
      }

  Iₛ : Setoid (a ⊔ b ⊔ ℓ) (a ⊔ b ⊔ ℓ)
  Iₛ = record 
    { _≈_           = _≈ⁱ_
    ; isEquivalence = ≈ⁱ-isEquivalence
    }

  -- A routing algebra can now be formed
  ira : RoutingAlgebra _ _ _
  ira = record 
    { Step  = IStep
    ; Route = IRoute
    ; _⊕_   = _⊕ⁱ_
    ; _▷_   = _▷ⁱ_
    ; 0#    = inull
    ; 1#    = iroute 1# []

    ; _≈_                = _≈ⁱ_
    ; ≈-isDecEquivalence = ≈ⁱ-isDecEquivalence
    ; ▷-pres-≈           = ▷ⁱ-pres-≈ⁱ
    ; ⊕-pres-≈           = ⊕ⁱ-pres-≈ⁱ
    }


  ---------------------
  -- Routing problem --
  ---------------------

  Aⁱ : Fin n → Fin n → IStep
  Aⁱ i j = (i , j)

  irp : RoutingProblem _ _ _ n
  irp = record {
       ra = ira;
       A = Aⁱ
    }

  -----------
  -- Other --
  -----------

  size : IRoute → ℕ
  size inull        = 0
  size (iroute _ p) = length p
