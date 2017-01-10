

open import Algebra.FunctionProperties using (Op₂)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_; lookup; foldr₁; foldr; allFin)
open import Function using (_∘_)
open import Level using (_⊔_) renaming (suc to lsuc)
open import Relation.Binary using (Rel; IsDecEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; [_]; subst; subst₂) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Algebra.FunctionProperties using (Selective)
open import RoutingLib.Data.Graph using (Graph; _ᵉ∈ᵍ?_)
open import RoutingLib.Data.Graph.EPath using (_∷_; _≈ₚ_) renaming (source to sourceⁱ; _∉?_ to _∉ⁱ?_)
open import RoutingLib.Data.Graph.EPath.Properties using (≈ₚ-refl; ≈ₚ-sym)
open import RoutingLib.Data.Graph.EGPath using (toEPath) renaming (source to sourceᶜ)
open import RoutingLib.Data.Graph.EGPath.Properties using (toEPath-source; toEPath-∉₁; toEPath-∉₂) renaming (_∉?_ to _∉ᶜ?_)
open import RoutingLib.Data.Maybe.Properties using (just-injective)
open import RoutingLib.Data.Vec.Properties using (lookup-map)
open import RoutingLib.Routing.Definitions

module RoutingLib.Routing.AddingPaths.Bisimilarity
  {a b ℓ} (ra : RoutingAlgebra a b ℓ) 
  (⊕-sel : Selective (RoutingAlgebra._≈_ ra) (RoutingAlgebra._⊕_ ra))
  (one : (RoutingAlgebra.Route ra))
  {n : ℕ}
  (G : Graph (RoutingAlgebra.Step ra) n)
  where

  open RoutingAlgebra ra

  open import RoutingLib.Routing.AddingPaths.Consistent ra ⊕-sel one G hiding (select; sel₁; sel₂; sel≈; ≤ₗₚ-resp-≈ₚ) renaming (_≤ₗₚ?_ to  _≤ₗₚᶜ?_)
  open import RoutingLib.Routing.AddingPaths.Inconsistent ra ⊕-sel one G renaming (_≤ₗₚ?_ to _≤ₗₚⁱ?_)

  open import RoutingLib.Routing.Algorithms.DistributedBellmanFord
  open import RoutingLib.Routing.Algorithms.DistributedBellmanFord.Properties

  infix 4 _≃_
  infix 4 _≃ₘ_

  ------------------
  -- Bisimilarity --
  ------------------
  
  drop : CRoute → IRoute
  drop cnull          = inull
  drop (croute x p _) = iroute x (toEPath p)

  data _≃_ : CRoute → IRoute → Set (a ⊔ b ⊔ ℓ) where
    nullEq  : cnull ≃ inull
    routeEq : ∀ {x p y q x≈w[p]} → x ≈ y → toEPath p ≈ₚ q → croute x p x≈w[p] ≃ iroute y q

  _≃ₘ_ : RMatrix crp → RMatrix irp → Set (a ⊔ b ⊔ ℓ)
  X ≃ₘ Y = ∀ i j → X i j ≃ Y i j

  abstract

    ⊕-≃ : ∀ {w x y z} → w ≃ x → y ≃ z → w ⊕ᶜ y ≃ x ⊕ⁱ z
    ⊕-≃ nullEq            nullEq = nullEq
    ⊕-≃ nullEq            y≃z    = y≃z
    ⊕-≃ (routeEq w≈x p≈q) nullEq = routeEq w≈x p≈q
    ⊕-≃ {croute w p _} {iroute x q} {croute y r _} {iroute z s} (routeEq w≈x p≈q) (routeEq y≈z r≈s) with select w y | select x z
    ... | sel₁ _     _     | sel₁ _     _     = routeEq w≈x p≈q
    ... | sel₁ w⊕y≈w _     | sel₂ x⊕z≉x _     = contradiction (trans (trans (⊕-pres-≈ (sym w≈x) (sym y≈z)) w⊕y≈w) w≈x) x⊕z≉x
    ... | sel₁ _     w⊕y≉y | sel≈ _     x⊕z≈z = contradiction (trans (trans (⊕-pres-≈ w≈x y≈z) x⊕z≈z) (sym y≈z)) w⊕y≉y
    ... | sel₂ w⊕y≉w _     | sel₁ x⊕z≈x _     = contradiction (trans (trans (⊕-pres-≈ w≈x y≈z) x⊕z≈x) (sym w≈x)) w⊕y≉w
    ... | sel₂ _     _     | sel₂ _     _     = routeEq y≈z r≈s
    ... | sel₂ w⊕y≉w _     | sel≈ x⊕z≈x _     = contradiction (trans (trans (⊕-pres-≈ w≈x y≈z) x⊕z≈x) (sym w≈x)) w⊕y≉w
    ... | sel≈ _     w⊕y≈y | sel₁ _     x⊕z≉z = contradiction (trans (trans (⊕-pres-≈ (sym w≈x) (sym y≈z)) w⊕y≈y) y≈z) x⊕z≉z
    ... | sel≈ w⊕y≈w _     | sel₂ x⊕z≉x _     = contradiction (trans (trans (⊕-pres-≈ (sym w≈x) (sym y≈z)) w⊕y≈w) w≈x) x⊕z≉x
    ... | sel≈ _     _     | sel≈ _     _     with p ≤ₗₚᶜ? r | q ≤ₗₚⁱ? s
    ...   | yes _   | yes _   = routeEq w≈x p≈q
    ...   | yes p≤r | no  q≰s = contradiction (≤ₗₚ-resp-≈ₚ p≈q r≈s p≤r) q≰s
    ...   | no  p≰r | yes q≤s = contradiction (≤ₗₚ-resp-≈ₚ (≈ₚ-sym p≈q) (≈ₚ-sym r≈s) q≤s) p≰r
    ...   | no  _   | no  _   = routeEq y≈z r≈s

    ▷-≃ : ∀ {i j w} {x : CRoute} {y : IRoute} → G i j ≡ just w → x ≃ y → cedge (i , j , w) ▷ᶜ x ≃ iedge (i , j , w) ▷ⁱ y
    ▷-≃ {x = cnull} {y = inull}      _               nullEq           = nullEq
    ▷-≃ {i} {j} {w} {croute x p _} {iroute y q} e∈G (routeEq x≈y p≈q) with j ≟ᶠ sourceᶜ p | j ≟ᶠ sourceⁱ q | i ∉ᶜ? p | i ∉ⁱ? q | (i , j) ᵉ∈ᵍ? G
    ... | no  _    | no _     | _       | _       | _             = nullEq
    ... | no  j≢p₀ | yes j≡q₀ | _       | _       | _             = contradiction (≡-trans j≡q₀ (≡-sym (toEPath-source p≈q))) j≢p₀
    ... | yes j≡p₀ | no  j≢q₀ | _       | _       | _             = contradiction (≡-trans j≡p₀ (toEPath-source p≈q)) j≢q₀
    ... | yes _    | yes _    | no  _   | no _    | _             = nullEq
    ... | yes _    | yes _    | yes i∉p | no  i∈q | _             = contradiction (toEPath-∉₁ p≈q i∉p) i∈q
    ... | yes _    | yes _    | no  i∈p | yes i∉q | _             = contradiction (toEPath-∉₂ p≈q i∉q) i∈p
    ... | yes _    | yes _    | yes _   | yes _   | no  e∉G       = contradiction (w , e∈G) e∉G
    ... | yes _    | yes _    | yes _   | yes _   | yes (v , e∈G₂) = routeEq (subst (λ u → v ▷ x ≈ u ▷ y) (just-injective (≡-trans (≡-sym e∈G₂) e∈G)) (▷-pres-≈ v x≈y)) (≡-refl ∷ p≈q)


    ---------------------
    -- DBF preserves ≃ --
    ---------------------
  
    Iᶜ≃Iⁱ : Iᶜ ≃ₘ Iⁱ
    Iᶜ≃Iⁱ i j with j ≟ᶠ i
    ... | no  _ = nullEq
    ... | yes _ = routeEq refl ≈ₚ-refl

    ⊕ₘ-≃ : ∀ {X₁ X₂ Y₁ Y₂} → X₁ ≃ₘ Y₁ → X₂ ≃ₘ Y₂ → _⊕ₘ_ crp X₁ X₂ ≃ₘ _⊕ₘ_ irp Y₁ Y₂
    ⊕ₘ-≃ X₁≃Y₁ X₂≃Y₂ i j = ⊕-≃ (X₁≃Y₁ i j) (X₂≃Y₂ i j)

    foldr₁-≃ : ∀ {n} {xs : Vec CRoute (suc n)} {ys : Vec IRoute (suc n)} → (∀ i → lookup i xs ≃ lookup i ys) → foldr₁ _⊕ᶜ_ xs ≃ foldr₁ _⊕ⁱ_ ys
    foldr₁-≃ {xs = x ∷ []} {ys = y ∷ []} xsᵢ≃ysᵢ = xsᵢ≃ysᵢ fzero
    foldr₁-≃ {xs = x₁ ∷ x₂ ∷ xs} {ys = y₁ ∷ y₂ ∷ ys} xsᵢ≃ysᵢ = ⊕-≃ (xsᵢ≃ysᵢ fzero) (foldr₁-≃ (xsᵢ≃ysᵢ ∘ fsuc))

    foldr-≃ : ∀ {n} {e f} → e ≃ f → {xs : Vec CRoute n} {ys : Vec IRoute n} → (∀ i → lookup i xs ≃ lookup i ys) → foldr (λ _ → CRoute) _⊕ᶜ_ e xs ≃ foldr (λ _ → IRoute) _⊕ⁱ_ f ys
    foldr-≃ e≃f {xs = []}     {ys = []}     xsᵢ≃ysᵢ = e≃f
    foldr-≃ e≃f {xs = x ∷ xs} {ys = y ∷ ys} xsᵢ≃ysᵢ = ⊕-≃ (xsᵢ≃ysᵢ fzero) (foldr-≃ e≃f (xsᵢ≃ysᵢ ∘ fsuc))

    A▷-≃ : ∀ {X Y i j k} → X ≃ₘ Y → Aᶜ i k ▷ᶜ X k j ≃ Aⁱ i k ▷ⁱ Y k j
    A▷-≃ {i = i} {j} {k} X≃Y with G i k | inspect (λ i → G i k) i
    ... | nothing | _            = nullEq
    ... | just v  | [ Gᵢₖ≡justv ] = ▷-≃ Gᵢₖ≡justv (X≃Y k j)

    extensions-≃ : ∀ {X Y i j} → X ≃ₘ Y → ∀ l → lookup l (extensions crp X i j) ≃ lookup l (extensions irp Y i j)
    extensions-≃ X≃Y l = subst₂ _≃_ (≡-sym (lookup-map l (allFin n))) (≡-sym (lookup-map l (allFin n))) (A▷-≃ X≃Y)

    σ-≃ : ∀ {X Y} → X ≃ₘ Y → σ crp X  ≃ₘ σ irp Y
    σ-≃ X≃Y i j = foldr-≃ (Iᶜ≃Iⁱ i j) (extensions-≃ X≃Y)

    σ^-≃ : ∀ {X Y} k → X ≃ₘ Y → σ^ crp k X ≃ₘ σ^ irp k Y
    σ^-≃ zero    X≃Y = X≃Y
    σ^-≃ (suc k) X≃Y = σ-≃ (σ^-≃ k X≃Y)

