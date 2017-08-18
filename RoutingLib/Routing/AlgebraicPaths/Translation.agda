open import Data.Nat using (ℕ)
open import Relation.Nullary using (¬_; yes; no)
open import Data.Product using (Σ; _,_)
open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_)
open import Data.List using (map; foldr)
open import Data.List.All using (All; []; _∷_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (_Preserves_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; cong) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Algebra.FunctionProperties using (Selective)
open import Relation.Binary.List.Pointwise using ([]; _∷_) renaming (Rel to ListRel)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Data.Graph using (Graph; _∈?_)
open import RoutingLib.Data.Graph.SimplePath using ([]; [_]; source)
open import RoutingLib.Data.Graph.SimplePath.Properties using (_≤ₚ?_; _∉?_) renaming (_≟_ to _≟ₚ_; ≈-refl to ≈ₚ-refl)

module RoutingLib.Routing.AlgebraicPaths.Translation
  {a b ℓ}
  (𝓡𝓐 : RoutingAlgebra a b ℓ)
  (⊕-sel : Selective (RoutingAlgebra._≈_ 𝓡𝓐) (RoutingAlgebra._⊕_ 𝓡𝓐))
  {n : ℕ}
  (G : Graph (RoutingAlgebra.Step 𝓡𝓐) n)
  where

  open RoutingAlgebra 𝓡𝓐
  
  open import RoutingLib.Routing.AlgebraicPaths.Consistent 𝓡𝓐 ⊕-sel G hiding (⊕-select; sel₁; sel₂; sel≈; size)
  open import RoutingLib.Routing.AlgebraicPaths.Inconsistent 𝓡𝓐 ⊕-sel G

  open RoutingProblem 𝓡𝓟ᶜ using () renaming (RMatrix to CMatrix; _≈ₘ_ to _≈ᶜₘ_; _≉ₘ_ to _≉ᶜₘ_)
  open RoutingProblem 𝓡𝓟ⁱ using () renaming (RMatrix to IMatrix; _≈ₘ_ to _≈ⁱₘ_; _≉ₘ_ to _≉ⁱₘ_; ≉ₘ-witness to ≉ⁱₘ-witness)

  open import RoutingLib.Routing.AlgebraicPaths.Inconsistent.Properties 𝓡𝓐 ⊕-sel G

  ----------------------------------------------------------------------------
  -- Conversion between CRoutes and IRoutes

  toI : CRoute → IRoute
  toI cnull            = inull
  toI (croute x p _ _) = iroute x p

  toIₘ : CMatrix → IMatrix
  toIₘ Xᶜ i j = toI (Xᶜ i j)
  
  fromI : ∀ {r} → 𝑪 r → CRoute
  fromI 𝒄-null               = cnull
  fromI (𝒄-route p∈G x≈w[p]) = croute _ _ p∈G x≈w[p]

  fromIₘ : ∀ {X} → 𝑪ₘ X → CMatrix
  fromIₘ Xᶜ i j = fromI (Xᶜ i j)
  
  abstract

    ----------------------------------------------------------------------------
    -- Properties

    toI-cong : toI Preserves _≈ᶜ_ ⟶ _≈ⁱ_
    toI-cong cnullEq            = inullEq
    toI-cong (crouteEq x≈y p≈q) = irouteEq x≈y p≈q

    toI-injective : ∀ {x y} → toI x ≈ⁱ toI y → x ≈ᶜ y
    toI-injective {cnull}          {cnull}          _                  = cnullEq
    toI-injective {cnull}          {croute y q _ _} ()
    toI-injective {croute x p _ _} {cnull}          ()
    toI-injective {croute x p _ _} {croute y q _ _} (irouteEq x≈y p≈q) = crouteEq x≈y p≈q

    toIᶜ : ∀ x → 𝑪 (toI x)
    toIᶜ cnull                 = 𝒄-null
    toIᶜ (croute x p p∈G x≈wₚ) = 𝒄-route p∈G x≈wₚ
    
    toIₘ-cong : toIₘ Preserves _≈ᶜₘ_ ⟶ _≈ⁱₘ_
    toIₘ-cong X≈Y i j = toI-cong (X≈Y i j)

    toIₘ-injective : ∀ {X Y} → toIₘ X ≈ⁱₘ toIₘ Y → X ≈ᶜₘ Y
    toIₘ-injective toX≈toY i j = toI-injective (toX≈toY i j)

    toIₘᶜ : ∀ X → 𝑪ₘ (toIₘ X)
    toIₘᶜ X i j = toIᶜ (X i j)




    fromI-cong : ∀ {x y} (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) → x ≈ⁱ y → fromI xᶜ ≈ᶜ fromI yᶜ
    fromI-cong 𝒄-null        𝒄-null        inullEq            = cnullEq
    fromI-cong (𝒄-route _ _) (𝒄-route _ _) (irouteEq x≈y p≈q) = crouteEq x≈y p≈q

    fromI-injective : ∀ {x y} (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) → fromI xᶜ ≈ᶜ fromI yᶜ → x ≈ⁱ y
    fromI-injective 𝒄-null        𝒄-null        cnullEq            = inullEq
    fromI-injective 𝒄-null        (𝒄-route _ _) ()
    fromI-injective (𝒄-route _ _) 𝒄-null ()
    fromI-injective (𝒄-route _ _) (𝒄-route _ _) (crouteEq x≈y p≈q) = irouteEq x≈y p≈q
    
    fromI-¬cong : ∀ {x y} (xᶜ : 𝑪 x) (yᶜ : 𝑪 y) → x ≉ⁱ y → fromI xᶜ ≉ᶜ fromI yᶜ
    fromI-¬cong 𝒄-null        𝒄-null        x≉y _                  = x≉y inullEq
    fromI-¬cong 𝒄-null        (𝒄-route _ _) _   ()
    fromI-¬cong (𝒄-route _ _) 𝒄-null        _   ()
    fromI-¬cong (𝒄-route _ _) (𝒄-route _ _) x≉y (crouteEq x≈y p≈q) = x≉y (irouteEq x≈y p≈q)

    fromIₘ-cong : ∀ {X Y} (Xᶜ : 𝑪ₘ X) (Yᶜ : 𝑪ₘ Y) → X ≈ⁱₘ Y → fromIₘ Xᶜ ≈ᶜₘ fromIₘ Yᶜ
    fromIₘ-cong Xᶜ Yᶜ X≈Y i j = fromI-cong (Xᶜ i j) (Yᶜ i j) (X≈Y i j)

    fromIₘ-injective : ∀ {X Y} (Xᶜ : 𝑪ₘ X) (Yᶜ : 𝑪ₘ Y) → fromIₘ Xᶜ ≈ᶜₘ fromIₘ Yᶜ → X ≈ⁱₘ Y
    fromIₘ-injective Xᶜ Yᶜ fX≈fY = λ i j → fromI-injective (Xᶜ i j) (Yᶜ i j) (fX≈fY i j)
    
    fromIₘ-¬cong : ∀ {X Y} (Xᶜ : 𝑪ₘ X) (Yᶜ : 𝑪ₘ Y) → X ≉ⁱₘ Y → fromIₘ Xᶜ ≉ᶜₘ fromIₘ Yᶜ
    fromIₘ-¬cong Xᶜ Yᶜ X≉Y X≈Y with ≉ⁱₘ-witness X≉Y
    ... | (i , j , Xᵢⱼ≉Yᵢⱼ) = fromI-¬cong (Xᶜ i j) (Yᶜ i j) Xᵢⱼ≉Yᵢⱼ (X≈Y i j)

    fromI-toI : ∀ {x} (xᶜ : 𝑪 (toI x)) → fromI xᶜ ≈ᶜ x
    fromI-toI {cnull}          𝒄-null        = cnullEq
    fromI-toI {croute _ _ _ _} (𝒄-route _ _) = crouteEq refl ≈ₚ-refl

    fromIₘ-toIₘ : ∀ {X} (Xᶜ : 𝑪ₘ (toIₘ X)) → fromIₘ Xᶜ ≈ᶜₘ X
    fromIₘ-toIₘ Xᶜ i j = fromI-toI (Xᶜ i j)


    


    ▷-fromI-commute : ∀ {v r} (rᶜ : 𝑪 r) (v▷rᶜ : 𝑪 (v ▷ⁱ r)) → fromI v▷rᶜ ≈ᶜ v ▷ᶜ fromI rᶜ
    ▷-fromI-commute {_}     {inull}          𝒄-null        𝒄-null = cnullEq
    ▷-fromI-commute {i , j} {iroute x []}    (𝒄-route [] _) v▷rᶜ with i ≟𝔽 j | (i , j) ∈? G | v▷rᶜ
    ... | yes _ | _           | 𝒄-null = cnullEq
    ... | no  _ | no  _       | 𝒄-null = cnullEq
    ... | no  _ | yes (v , _) | v▷rᶜ' with v ▷ x ≟ 0# | v▷rᶜ'
    ...   | yes _ | 𝒄-null      = cnullEq
    ...   | no  _ | 𝒄-route _ _ = crouteEq refl ≈ₚ-refl
    ▷-fromI-commute {i , j} {iroute x [ p ]} (𝒄-route [ _ ] _) v▷rᶜ with j ≟𝔽 source p | i ∉? [ p ] | (i , j) ∈? G | v▷rᶜ
    ... | no  _ | _         | _           | 𝒄-null = cnullEq
    ... | yes _ | no  _     | _           | 𝒄-null = cnullEq
    ... | yes _ | yes _     | no _        | 𝒄-null = cnullEq
    ... | yes _ | yes [ _ ] | yes (v , _) | v▷rᶜ'  with v ▷ x ≟ 0# | v▷rᶜ'
    ...   | yes _ | 𝒄-null  = cnullEq
    ...   | no  _ | 𝒄-route _ _ = crouteEq refl ≈ₚ-refl

    ⊕-fromI-commute : ∀ {r s} (rᶜ : 𝑪 r) (sᶜ : 𝑪 s) (r⊕sᶜ : 𝑪 (r ⊕ⁱ s)) →
                      fromI r⊕sᶜ ≈ᶜ (fromI rᶜ) ⊕ᶜ (fromI sᶜ)
    ⊕-fromI-commute 𝒄-null        𝒄-null        𝒄-null        = cnullEq
    ⊕-fromI-commute 𝒄-null        (𝒄-route _ _) (𝒄-route _ _) = crouteEq refl ≈ₚ-refl
    ⊕-fromI-commute (𝒄-route _ _) 𝒄-null        (𝒄-route _ _) = crouteEq refl ≈ₚ-refl
    ⊕-fromI-commute {iroute x p} {iroute y q} (𝒄-route _ _) (𝒄-route _ _) r⊕sᶜ with ⊕-select x y | r⊕sᶜ
    ... | sel₁ _ _ | 𝒄-route _ _ = crouteEq refl ≈ₚ-refl
    ... | sel₂ _ _ | 𝒄-route _ _ = crouteEq refl ≈ₚ-refl
    ... | sel≈ _ _ | r⊕sᶜ' with p ≤ₚ? q | r⊕sᶜ'
    ...   | yes _ | 𝒄-route _ _ = crouteEq refl ≈ₚ-refl
    ...   | no  _ | 𝒄-route _ _ = crouteEq refl ≈ₚ-refl

    foldr-fromI-commute : ∀ {e f} (eᶜ : 𝑪 e) → fromI eᶜ ≈ᶜ f → 
                          ∀ {xs ys} (foldrᶜ : 𝑪 (foldr _⊕ⁱ_ e xs)) →
                          ListRel (λ x y → Σ (𝑪 x) (λ xᶜ → fromI xᶜ ≈ᶜ y)) xs ys →
                          fromI foldrᶜ ≈ᶜ foldr _⊕ᶜ_ f ys
    foldr-fromI-commute eᶜ e≈f foldrᶜ []                   = ≈ᶜ-trans (fromI-cong foldrᶜ eᶜ ≈ⁱ-refl) e≈f
    foldr-fromI-commute eᶜ e≈f foldrᶜ ((xᶜ , x≈y) ∷ xs≈ys) = ≈ᶜ-trans (⊕-fromI-commute xᶜ (foldrᶜ-lemma eᶜ xs≈ys) foldrᶜ) (⊕ᶜ-cong x≈y (foldr-fromI-commute eᶜ e≈f (foldrᶜ-lemma eᶜ xs≈ys) xs≈ys))
      where
      foldrᶜ-lemma : ∀ {e xs ys} → 𝑪 e → ListRel (λ x y → Σ (𝑪 x) (λ xᶜ → fromI xᶜ ≈ᶜ y)) xs ys → 𝑪 (foldr _⊕ⁱ_ e xs)
      foldrᶜ-lemma eᶜ [] = eᶜ
      foldrᶜ-lemma eᶜ ((xᶜ , _) ∷ xs≈ys) = ⊕ⁱ-pres-𝑪 xᶜ (foldrᶜ-lemma eᶜ xs≈ys)
      
