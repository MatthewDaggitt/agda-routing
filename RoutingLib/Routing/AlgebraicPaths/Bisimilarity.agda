open import Algebra.FunctionProperties using (Op₂; Selective)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_; lookup; map; foldr₁; foldr; allFin)
open import Function using (_∘_)
open import Level using (_⊔_) renaming (suc to lsuc)
open import Relation.Binary using (Rel; IsDecEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; [_]; subst; subst₂) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Graph using (Graph; _∈?_; _∈_)
open import RoutingLib.Data.Graph.SimplePath using ([]; [_]; _∷_; _∺_; source) renaming (_≈_ to _≈ₚ_)
open import RoutingLib.Data.Graph.SimplePath.Properties using (_≤ₚ?_; _∉?_; ∉-resp-≈; ≤ₚ-resp-≈; p≈q⇒p₀≡q₀) renaming (≈-refl to ≈ₚ-refl; ≈-sym to ≈ₚ-sym; ≈-trans to ≈ₚ-trans)
open import RoutingLib.Data.Maybe.Properties using (just-injective)
open import RoutingLib.Data.Vec.Properties using (lookup-map)
open import RoutingLib.Routing.Definitions


module RoutingLib.Routing.AlgebraicPaths.Bisimilarity
  {a b ℓ} (ra : RoutingAlgebra a b ℓ)
  (⊕-sel : Selective (RoutingAlgebra._≈_ ra) (RoutingAlgebra._⊕_ ra))
  {n : ℕ}
  (G : Graph (RoutingAlgebra.Step ra) n)
  where

  open RoutingAlgebra ra

  open import RoutingLib.Routing.AlgebraicPaths.Consistent ra ⊕-sel G hiding (select; sel₁; sel₂; sel≈)
  open import RoutingLib.Routing.AlgebraicPaths.Inconsistent ra ⊕-sel G

  private
    module I = RoutingProblem irp
    module C = RoutingProblem crp

  ------------------
  -- Bisimilarity --
  ------------------

  infix 4 _≃_ _≃ₘ_

  data _≃_ : IRoute → CRoute → Set (a ⊔ b ⊔ ℓ) where
    nullEq  : inull ≃ cnull
    routeEq : ∀ {x p y q q∈G y≈w[q]} → x ≈ y → p ≈ₚ q → iroute x p ≃ croute y q q∈G y≈w[q]

  _≃ₘ_ : I.RMatrix → C.RMatrix → Set (a ⊔ b ⊔ ℓ)
  X ≃ₘ Y = ∀ i j → X i j ≃ Y i j

  abstract

    toIRoute-≃ : ∀ x → toIRoute x ≃ x
    toIRoute-≃ cnull = nullEq
    toIRoute-≃ (croute x p _ _) = routeEq refl ≈ₚ-refl

    ⊕-≃ : ∀ {w x y z} → w ≃ x → y ≃ z → w ⊕ⁱ y ≃ x ⊕ᶜ z
    ⊕-≃ nullEq            nullEq = nullEq
    ⊕-≃ nullEq            y≃z    = y≃z
    ⊕-≃ (routeEq w≈x p≈q) nullEq = routeEq w≈x p≈q
    ⊕-≃ {iroute w p} {croute x q _ _} {iroute y r} {croute z s _ _} (routeEq w≈x p≈q) (routeEq y≈z r≈s) with select w y | select x z
    ... | sel₁ _     _     | sel₁ _     _     = routeEq w≈x p≈q
    ... | sel₁ w⊕y≈w _     | sel₂ x⊕z≉x _     = contradiction (trans (trans (⊕-pres-≈ (sym w≈x) (sym y≈z)) w⊕y≈w) w≈x) x⊕z≉x
    ... | sel₁ _     w⊕y≉y | sel≈ _     x⊕z≈z = contradiction (trans (trans (⊕-pres-≈ w≈x y≈z) x⊕z≈z) (sym y≈z)) w⊕y≉y
    ... | sel₂ w⊕y≉w _     | sel₁ x⊕z≈x _     = contradiction (trans (trans (⊕-pres-≈ w≈x y≈z) x⊕z≈x) (sym w≈x)) w⊕y≉w
    ... | sel₂ _     _     | sel₂ _     _     = routeEq y≈z r≈s
    ... | sel₂ w⊕y≉w _     | sel≈ x⊕z≈x _     = contradiction (trans (trans (⊕-pres-≈ w≈x y≈z) x⊕z≈x) (sym w≈x)) w⊕y≉w
    ... | sel≈ _     w⊕y≈y | sel₁ _     x⊕z≉z = contradiction (trans (trans (⊕-pres-≈ (sym w≈x) (sym y≈z)) w⊕y≈y) y≈z) x⊕z≉z
    ... | sel≈ w⊕y≈w _     | sel₂ x⊕z≉x _     = contradiction (trans (trans (⊕-pres-≈ (sym w≈x) (sym y≈z)) w⊕y≈w) w≈x) x⊕z≉x
    ... | sel≈ _     _     | sel≈ _     _     with p ≤ₚ? r | q ≤ₚ? s
    ...   | yes _   | yes _   = routeEq w≈x p≈q
    ...   | yes p≤r | no  q≰s = contradiction (≤ₚ-resp-≈ p≈q r≈s p≤r) q≰s
    ...   | no  p≰r | yes q≤s = contradiction (≤ₚ-resp-≈ (≈ₚ-sym p≈q) (≈ₚ-sym r≈s) q≤s) p≰r
    ...   | no  _   | no  _   = routeEq y≈z r≈s

    ▷-≃ : ∀ s {x y} → x ≃ y → s ▷ⁱ x ≃ s ▷ᶜ y
    ▷-≃ _       {inull}          {cnull}           nullEq           = nullEq
    ▷-≃ (i , j) {iroute x []}    {croute y [] [] y≈1} (routeEq x≈y []) with i ≟ᶠ j | (i , j) ∈? G
    ... | yes _ | _           = nullEq
    ... | no  _ | no  _       = nullEq
    ... | no  _ | yes (v , _) with v ▷ x ≟ 0# | v ▷ y ≟ 0#
    ...   | yes _     | yes _     = nullEq
    ...   | yes v▷x≈0 | no  v▷y≉0 = contradiction (trans (▷-pres-≈ v (sym x≈y)) v▷x≈0) v▷y≉0
    ...   | no  v▷x≉0 | yes v▷y≈0 = contradiction (trans (▷-pres-≈ v x≈y) v▷y≈0) v▷x≉0
    ...   | no  _     | no _      = routeEq (▷-pres-≈ v x≈y) [ ≡-refl ∺ ≡-refl ]
    ▷-≃ _       {iroute _ [ _ ]} {croute _ []    _     _} (routeEq x≈y ())
    ▷-≃ _       {iroute _ []}    {croute _ [ _ ] _     _} (routeEq x≈y ())
    ▷-≃ (i , j) {iroute x [ p ]} {croute y [ q ] [ _ ] _} (routeEq x≈y [ p≈q ]) with j ≟ᶠ source p | j ≟ᶠ source q | i ∉? [ p ] | i ∉? [ q ] | (i , j) ∈? G
    ... | no  _    | no _     | _         | _       | _           = nullEq
    ... | no  j≢p₀ | yes j≡q₀ | _         | _       | _           = contradiction (≡-trans j≡q₀ (≡-sym (p≈q⇒p₀≡q₀ p≈q))) j≢p₀
    ... | yes j≡p₀ | no  j≢q₀ | _         | _       | _           = contradiction (≡-trans j≡p₀ (p≈q⇒p₀≡q₀ p≈q)) j≢q₀
    ... | yes _    | yes _    | no  _     | no _    | _           = nullEq
    ... | yes _    | yes _    | yes i∉p   | no  i∈q | _           = contradiction (∉-resp-≈ [ p≈q ] i∉p) i∈q
    ... | yes _    | yes _    | no  i∈p   | yes i∉q | _           = contradiction (∉-resp-≈ (≈ₚ-sym [ p≈q ]) i∉q) i∈p
    ... | yes _    | yes _    | yes _     | yes _   | no  _       = nullEq
    ... | yes _    | yes _    | yes [ _ ] | yes [ _ ] | yes (v , _) with v ▷ x ≟ 0# | v ▷ y ≟ 0#
    ...   | yes _     | yes _     = nullEq
    ...   | yes v▷x≈0 | no  v▷y≉0 = contradiction (trans (▷-pres-≈ v (sym x≈y)) v▷x≈0) v▷y≉0
    ...   | no  v▷x≉0 | yes v▷y≈0 = contradiction (trans (▷-pres-≈ v x≈y) v▷y≈0) v▷x≉0
    ...   | no  _     | no _      = routeEq (▷-pres-≈ v x≈y) [ ≡-refl ∷ p≈q ]

    foldr-≃ : ∀ {n} {e f} → e ≃ f → ∀ {xs ys} → (∀ (i : Fin n) → lookup i xs ≃ lookup i ys) → foldr (λ _ → IRoute) _⊕ⁱ_ e xs ≃ foldr (λ _ → CRoute) _⊕ᶜ_ f ys
    foldr-≃ e≃f {[]}     {[]}     xsᵢ≃ysᵢ = e≃f
    foldr-≃ e≃f {x ∷ xs} {y ∷ ys} xsᵢ≃ysᵢ = ⊕-≃ (xsᵢ≃ysᵢ fzero) (foldr-≃ e≃f (xsᵢ≃ysᵢ ∘ fsuc))

    map-≃ : ∀ {n l} {f g} → ∀ (xs : Vec (Fin n) l) → (∀ (i : Fin l) → f (lookup i xs) ≃ g (lookup i xs)) → ∀ i → lookup i (map f xs) ≃ lookup i (map g xs)
    map-≃ (_ ∷ _)  pres fzero    = pres fzero
    map-≃ (_ ∷ xs) pres (fsuc i) = map-≃ xs (pres ∘ fsuc) i


    ic+ic⇒cc : ∀ {x y z} → x ≃ y → x ≃ z → y ≈ᶜ z
    ic+ic⇒cc nullEq            nullEq            = cnullEq
    ic+ic⇒cc (routeEq x≈y p≈q) (routeEq x≈z p≈r) = crouteEq (trans (sym x≈y) x≈z) (≈ₚ-trans (≈ₚ-sym p≈q) p≈r)

    ic+cc⇒ic : ∀ {x y z} → x ≃ y → z ≈ᶜ y → x ≃ z
    ic+cc⇒ic nullEq            cnullEq            = nullEq
    ic+cc⇒ic (routeEq x≈y p≈q) (crouteEq z≈y r≈q) = routeEq (trans x≈y (sym z≈y)) (≈ₚ-trans p≈q (≈ₚ-sym r≈q))

    ic+ii⇒ic : ∀ {x y z} → x ≃ y → x ≈ⁱ z → z ≃ y
    ic+ii⇒ic nullEq            inullEq            = nullEq
    ic+ii⇒ic (routeEq x≈y p≈q) (irouteEq x≈z p≈r) = routeEq (trans (sym x≈z) x≈y) (≈ₚ-trans (≈ₚ-sym p≈r) p≈q)

    ic+ii⇒ii : ∀ {x y z} → x ≃ y → z ≃ y → x ≈ⁱ z
    ic+ii⇒ii nullEq            nullEq             = inullEq
    ic+ii⇒ii (routeEq x≈y p≈q) (routeEq z≈y r≈q)  = irouteEq (trans x≈y (sym z≈y)) (≈ₚ-trans p≈q (≈ₚ-sym r≈q))



    module InconsistentReasoning where

      abstract

        infix  3 _∎
        infixr 2 _≈ᶜ⟨_⟩_ _≈ⁱ⟨_⟩_ _≃ⁱᶜ⟨_⟩_ _≃ᶜⁱ⟨_⟩_
        infix  1 begin_

        begin_ : ∀{x y} → x ≈ⁱ y → x ≈ⁱ y
        begin_ x≈y = x≈y

        _≈ⁱ⟨_⟩_ : ∀ x {y z} → x ≈ⁱ y → y ≈ⁱ z → x ≈ⁱ z
        _ ≈ⁱ⟨ x≈y ⟩ y≈z = ≈ⁱ-trans x≈y y≈z

        _≈ᶜ⟨_⟩_ : ∀ {x y} z → z ≈ᶜ y → x ≃ y → x ≃ z
        _ ≈ᶜ⟨ z≈y ⟩ x≃y = ic+cc⇒ic x≃y z≈y

        _≃ⁱᶜ⟨_⟩_ : ∀ x {y z} → x ≃ y → z ≃ y → x ≈ⁱ z
        _ ≃ⁱᶜ⟨ x≃y ⟩ x≈z = ic+ii⇒ii x≃y x≈z

        _≃ᶜⁱ⟨_⟩_ : ∀ {x} y {z} → x ≃ y → x ≈ⁱ z → z ≃ y
        _ ≃ᶜⁱ⟨ x≃y ⟩ z≃y = ic+ii⇒ic x≃y z≃y

        _∎ : ∀ x → x ≈ⁱ x
        _ ∎ = ≈ⁱ-refl


    module BisimilarityReasoning where

      abstract

        infix  4 _∎
        infixr 3 _≃⟨_⟩_ _≈ⁱ⟨_⟩_
        infixr 2 _≈ᶜ⟨_⟩_
        infix  1 begin_

        begin_ : ∀{x y} → x ≃ y → x ≃ y
        begin_ x≈y = x≈y

        _≈ᶜ⟨_⟩_ : ∀ x {y z} → z ≈ᶜ y → x ≃ y → x ≃ z
        _ ≈ᶜ⟨ z≈y ⟩ x≃y = ic+cc⇒ic x≃y z≈y

        _≃⟨_⟩_ : ∀ x {y z} → x ≃ y → z ≈ᶜ y → x ≃ z
        _ ≃⟨ x≃y ⟩ z≈y = ic+cc⇒ic x≃y z≈y

        _≈ⁱ⟨_⟩_ : ∀ x {y} {z} → x ≈ⁱ y → y ≃ z → x ≃ z
        _ ≈ⁱ⟨ x≈y ⟩ y≈z = ic+ii⇒ic y≈z (≈ⁱ-sym x≈y)

        _∎ : ∀ x → x ≈ᶜ x
        _ ∎ = ≈ᶜ-refl

