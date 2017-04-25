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
open import Algebra.FunctionProperties using (Op₂; Selective; Congruent₂)

open import RoutingLib.Algebra.FunctionProperties using (_Preservesₗ_)
open import RoutingLib.Routing.Definitions
open import RoutingLib.Data.Graph using (Graph; _∈?_)
open import RoutingLib.Data.Graph.SimplePath renaming (_≈_ to _≈ₚ_; weight to weight')
open import RoutingLib.Data.Graph.SimplePath.Properties using (_≤ₚ?_; _∉?_; ≤ₚ-resp-≈; ∉-resp-≈; p≈q⇒p₀≡q₀) renaming (≈-refl to ≈ₚ-refl; ≈-sym to ≈ₚ-sym; ≈-trans to ≈ₚ-trans; _≟_ to _≟ₚ_)

open import RoutingLib.Relation.Binary.RespectedBy using (_RespectedBy_; Respects₂⇨RespectedBy)


module RoutingLib.Routing.AlgebraicPaths.Consistent
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

  weight : ∀ {p} → p ∈𝔾 G → Route
  weight = weight' _▷_ 1#

  data CRoute : Set (a ⊔ b ⊔ ℓ) where
    cnull  : CRoute
    croute : (x : Route) → (p : SimplePath n) → (p∈G : p ∈𝔾 G) → x ≈ weight p∈G → CRoute


  -- Step

  CStep : Set lzero
  CStep = Fin n × Fin n


  -- Equality

  infix 4 _≈ᶜ_ _≉ᶜ_

  data _≈ᶜ_ : Rel CRoute (a ⊔ b ⊔ ℓ) where
    cnullEq  : cnull ≈ᶜ cnull
    crouteEq : ∀ {x y p q p∈G q∈G x≈w[p] y≈w[q]} → x ≈ y → p ≈ₚ q → (croute x p p∈G x≈w[p]) ≈ᶜ (croute y q q∈G y≈w[q])

  _≉ᶜ_ : Rel CRoute (a ⊔ b ⊔ ℓ)
  x ≉ᶜ y = ¬ (x ≈ᶜ y)


  -- Choice operator

  infix 7 _⊕ᶜ_

  _⊕ᶜ_ : Op₂ CRoute
  cnull ⊕ᶜ r     = r
  r     ⊕ᶜ cnull = r
  (croute x p p∈G x≈w[p]) ⊕ᶜ (croute y q q∈G y≈w[q]) with select x y
  ... | sel₁ _ _ = croute x p p∈G x≈w[p]
  ... | sel₂ _ _ = croute y q q∈G y≈w[q]
  ... | sel≈ _ _ with p ≤ₚ? q
  ...   | yes _ = croute x p p∈G x≈w[p]
  ...   | no  _ = croute y q q∈G y≈w[q]


  -- Extension operator

  infix 6 _▷ᶜ_

  _▷ᶜ_ : CStep → CRoute → CRoute
  _       ▷ᶜ cnull              = cnull
  (i , j) ▷ᶜ (croute x [] [] x≈w[p]) with i ≟ᶠ j | (i , j) ∈? G
  ... | yes _  | _              = cnull
  ... | _      | no _           = cnull
  ... | no i≢j | yes (v , Gᵢⱼ≡v) with v ▷ x ≟ 0#
  ...   | yes _ = cnull
  ...   | no  _ = croute (v ▷ x) [ i ∺ j ∣ i≢j ] [ edge-∺ (v , Gᵢⱼ≡v) ] (▷-pres-≈ v x≈w[p])
  (i , j) ▷ᶜ (croute x [ p ] [ p∈G ] x≈w[p]) with j ≟ᶠ source p | i ∉? [ p ] | (i , j) ∈? G
  ... | no _       | _       | _              = cnull
  ... | _          | no  _   | _              = cnull
  ... | _          | _       | no _           = cnull
  ... | yes j≡p₀ | yes [ i∉p ] | yes (v , Gᵢⱼ≡v) with v ▷ x ≟ 0#
  ...   | yes _ = cnull
  ...   | no  _ = croute (v ▷ x) [ i ∷ p ∣ i∉p ] [ (edge-∷ (v , subst (λ j → G i j ≡ just v) j≡p₀ Gᵢⱼ≡v) p∈G) ] (▷-pres-≈ v x≈w[p])

  -- Equality properties

  abstract

    -- equality is a decidable equivalence

    ≈ᶜ-refl : Reflexive _≈ᶜ_
    ≈ᶜ-refl {cnull} = cnullEq
    ≈ᶜ-refl {croute _ _ _ _} = crouteEq refl ≈ₚ-refl

    ≈ᶜ-reflexive : _≡_ ⇒ _≈ᶜ_
    ≈ᶜ-reflexive ≡-refl = ≈ᶜ-refl

    ≈ᶜ-sym : Symmetric _≈ᶜ_
    ≈ᶜ-sym cnullEq            = cnullEq
    ≈ᶜ-sym (crouteEq x≈y p≈q) = crouteEq (sym x≈y) (≈ₚ-sym p≈q)

    ≈ᶜ-trans : Transitive _≈ᶜ_
    ≈ᶜ-trans cnullEq cnullEq = cnullEq
    ≈ᶜ-trans (crouteEq x≈y p≈q) (crouteEq y≈z q≈r) = crouteEq (trans x≈y y≈z) (≈ₚ-trans p≈q q≈r)

    _≟ᶜ_ : Decidable _≈ᶜ_
    cnull ≟ᶜ cnull = yes cnullEq
    cnull ≟ᶜ (croute _ _ _ _) = no λ()
    (croute _ _ _ _) ≟ᶜ cnull = no λ()
    (croute x p _ _) ≟ᶜ (croute y q _ _) with x ≟ y | p ≟ₚ q
    ... | no  x≉y | _       = no λ{(crouteEq x≈y _) → x≉y x≈y}
    ... | _       | no  p≉q = no λ{(crouteEq _ p≈q) → p≉q p≈q}
    ... | yes x≈y | yes p≈q = yes (crouteEq x≈y p≈q)

    ⊕ᶜ-pres-≈ᶜ : Congruent₂ _≈ᶜ_ _⊕ᶜ_
    ⊕ᶜ-pres-≈ᶜ cnullEq cnullEq = cnullEq
    ⊕ᶜ-pres-≈ᶜ cnullEq (crouteEq y≈z r≈s) = crouteEq y≈z r≈s
    ⊕ᶜ-pres-≈ᶜ (crouteEq w≈x p≈q) cnullEq = crouteEq w≈x p≈q
    ⊕ᶜ-pres-≈ᶜ {croute w p _ _} {croute x q _ _} {croute y r _ _} {croute z s _ _} (crouteEq w≈x p≈q) (crouteEq y≈z r≈s) with select w y | select x z
    ... | sel₁ _     _     | sel₁ _     _     = crouteEq w≈x p≈q
    ... | sel₁ _     w⊕y≉y | sel₂ _     x⊕z≈z = contradiction (trans (trans (⊕-pres-≈ w≈x y≈z) x⊕z≈z) (sym y≈z)) w⊕y≉y
    ... | sel₁ _     w⊕y≉y | sel≈ _     x⊕z≈z = contradiction (trans (trans (⊕-pres-≈ w≈x y≈z) x⊕z≈z) (sym y≈z)) w⊕y≉y
    ... | sel₂ w⊕y≉w _     | sel₁ x⊕z≈x _     = contradiction (trans (trans (⊕-pres-≈ w≈x y≈z) x⊕z≈x) (sym w≈x)) w⊕y≉w
    ... | sel₂ _     _     | sel₂ _     _     = crouteEq y≈z r≈s
    ... | sel₂ w⊕y≉w _     | sel≈ x⊕z≈x _     = contradiction (trans (trans (⊕-pres-≈ w≈x y≈z) x⊕z≈x) (sym w≈x)) w⊕y≉w
    ... | sel≈ _     w⊕y≈y | sel₁ _     x⊕z≉z = contradiction (trans (trans (sym (⊕-pres-≈ w≈x y≈z)) w⊕y≈y) y≈z) x⊕z≉z
    ... | sel≈ w⊕y≈w _     | sel₂ x⊕z≉x _     = contradiction (trans (trans (sym (⊕-pres-≈ w≈x y≈z)) w⊕y≈w) w≈x) x⊕z≉x
    ... | sel≈ _     _     | sel≈ _     _     with p ≤ₚ? r | q ≤ₚ? s
    ...   | yes _   | yes _   = crouteEq w≈x p≈q
    ...   | yes p≤r | no  q≰s = contradiction (≤ₚ-resp-≈ p≈q r≈s p≤r) q≰s
    ...   | no  p≰r | yes q≤s = contradiction (≤ₚ-resp-≈ (≈ₚ-sym p≈q) (≈ₚ-sym r≈s) q≤s) p≰r
    ...   | no  _   | no  _   = crouteEq y≈z r≈s

    ▷ᶜ-pres-≈ᶜ : _▷ᶜ_ Preservesₗ _≈ᶜ_
    ▷ᶜ-pres-≈ᶜ t cnullEq = cnullEq
    ▷ᶜ-pres-≈ᶜ (i , j) {croute x [] [] _} {croute y [] [] _} (crouteEq x≈y []) with i ≟ᶠ j | (i , j) ∈? G
    ... | yes _ | _     = ≈ᶜ-refl
    ... | no  _ | no  _ = ≈ᶜ-refl
    ... | no  _ | yes (v , _) with v ▷ x ≟ 0# | v ▷ y ≟ 0#
    ...   | yes _     | yes _     = cnullEq
    ...   | yes v▷x≈0 | no  v▷y≉0 = contradiction (trans (▷-pres-≈ v (sym x≈y)) v▷x≈0) v▷y≉0
    ...   | no  v▷x≉0 | yes v▷y≈0 = contradiction (trans (▷-pres-≈ v x≈y) v▷y≈0) v▷x≉0
    ...   | no  _     | no  _     = crouteEq (▷-pres-≈ v x≈y) ≈ₚ-refl
    ▷ᶜ-pres-≈ᶜ (i , j) {croute x [ p ] [ _ ] _} {croute y [ q ] [ _ ] _} (crouteEq x≈y [ p≈q ]) with j ≟ᶠ source p | j ≟ᶠ source q | i ∉? [ p ] | i ∉? [ q ] | (i , j) ∈? G
    ... | no  _    | no  _    | _       | _       | _           = cnullEq
    ... | no  j≢p₀ | yes j≡q₀ | _       | _       | _           = contradiction (≡-trans j≡q₀ (≡-sym (p≈q⇒p₀≡q₀ p≈q))) j≢p₀
    ... | yes j≡p₀ | no  j≢q₀ | _       | _       | _           = contradiction (≡-trans j≡p₀ (p≈q⇒p₀≡q₀ p≈q)) j≢q₀
    ... | yes _    | yes _    | no  _   | no  _   | _           = cnullEq
    ... | yes _    | yes _    | no  i∈p | yes i∉q | _           = contradiction (∉-resp-≈ (≈ₚ-sym [ p≈q ]) i∉q) i∈p
    ... | yes _    | yes _    | yes i∉p | no  i∈q | _           = contradiction (∉-resp-≈ [ p≈q ] i∉p) i∈q
    ... | yes _    | yes _    | yes _   | yes _   | no  _       = cnullEq
    ... | yes _    | yes _    | yes [ _ ] | yes [ _ ] | yes (v , _) with v ▷ x ≟ 0# | v ▷ y ≟ 0#
    ...   | yes _     | yes _     = cnullEq
    ...   | yes v▷x≈0 | no  v▷y≉0 = contradiction (trans (▷-pres-≈ v (sym x≈y)) v▷x≈0) v▷y≉0
    ...   | no  v▷x≉0 | yes v▷y≈0 = contradiction (trans (▷-pres-≈ v x≈y) v▷y≈0) v▷x≉0
    ...   | no  _     | no  _     = crouteEq (▷-pres-≈ v x≈y) [ ≡-refl ∷ p≈q ]

    ≈ᶜ-isEquivalence : IsEquivalence _≈ᶜ_
    ≈ᶜ-isEquivalence = record 
      { refl  = ≈ᶜ-refl 
      ; sym   = ≈ᶜ-sym 
      ; trans = ≈ᶜ-trans
      }

  ≈ᶜ-isDecEquivalence : IsDecEquivalence _≈ᶜ_
  ≈ᶜ-isDecEquivalence = record 
    { isEquivalence = ≈ᶜ-isEquivalence 
    ; _≟_           = _≟ᶜ_
    }

  Cₛ : Setoid (a ⊔ b ⊔ ℓ) (a ⊔ b ⊔ ℓ)
  Cₛ = record 
    { _≈_           = _≈ᶜ_
    ; isEquivalence = ≈ᶜ-isEquivalence
    }


  -- A routing algebra can now be formed

  cra : RoutingAlgebra _ _ _
  cra = record 
    { Step  = CStep
    ; Route = CRoute
    ; _⊕_   = _⊕ᶜ_
    ; _▷_   = _▷ᶜ_
    ; 0#    = cnull
    ; 1#    = croute 1# [] [] refl

    ; _≈_                = _≈ᶜ_
    ; ≈-isDecEquivalence = ≈ᶜ-isDecEquivalence
    ; ▷-pres-≈           = ▷ᶜ-pres-≈ᶜ
    ; ⊕-pres-≈           = ⊕ᶜ-pres-≈ᶜ
    }


  ---------------------
  -- Routing problem --
  ---------------------

  Aᶜ : Fin n → Fin n → CStep
  Aᶜ i j = i , j

  crp : RoutingProblem _ _ _ n
  crp = record 
    { ra = cra
    ; A  = Aᶜ
    }


  
  ---------------------
  -- Other functions --
  ---------------------

  open import RoutingLib.Routing.AlgebraicPaths.Inconsistent ra ⊕-sel G using (IRoute; iroute; inull)

  toIRoute : CRoute → IRoute
  toIRoute cnull            = inull
  toIRoute (croute x p _ _) = iroute x p

  pathToCRoute : ∀ {p} → p ∈𝔾 G → CRoute
  pathToCRoute {p} p∈G = croute (weight p∈G) p p∈G refl

  size : CRoute → ℕ
  size cnull            = 0
  size (croute _ p _ _) = length p
