open import Algebra.FunctionProperties
open import Data.List using (List; foldr)
open import Data.List.Any using (Any; here; there)
open import Data.List.All using (All; []; _∷_; lookup; map)
open import Data.List.Membership.Propositional using (_∈_; lose)
open import Data.List.Relation.Sublist.Propositional using (_⊆_)
open import Data.List.Properties using ()
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (id; flip; _on_)
open import Relation.Unary using (Pred)
open import Relation.Binary using (TotalOrder; Setoid)
import Relation.Binary.NonStrictToStrict as NonStrictToStrict
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)
import Relation.Binary.On as On

open import RoutingLib.Data.List.Properties
import RoutingLib.Algebra.Selectivity.NaturalChoice.Min as Min
import RoutingLib.Algebra.Selectivity.NaturalChoice.Max as Max
open import RoutingLib.Algebra.Selectivity.Lifting
open import Data.List.Membership.Propositional.Properties
  using (foldr-selective)

module RoutingLib.Data.List.Extrema
  {b ℓ₁ ℓ₂} (totalOrder : TotalOrder b ℓ₁ ℓ₂) where

  ------------------------------------------------------------------------------
  -- Setup

  open TotalOrder totalOrder renaming (Carrier to B)
  open NonStrictToStrict _≈_ _≤_ using (_<_)
  open import RoutingLib.Data.List.Extrema.Core totalOrder

  ------------------------------------------------------------------------------
  -- Functions

  argmin : ∀ {a} {A : Set a} (f : A → B) → A → List A → A
  argmin f = foldr (⊓-lift f)

  argmax : ∀ {a} {A : Set a} (f : A → B) → A → List A → A
  argmax f = foldr (⊔-lift f)
  
  min : B → List B → B
  min = argmin id

  max : B → List B → B
  max = argmax id

  ------------------------------------------------------------------------------
  -- Properties of argmin
  
  module _ {a} {A : Set a} {f : A → B} where
  
    f[argmin]≤v⁺ : ∀ {v} ⊤ xs → (f ⊤ ≤ v) ⊎ (Any (λ x → f x ≤ v) xs) →
                  f (argmin f ⊤ xs) ≤ v
    f[argmin]≤v⁺ = foldr-presᵒ (⊓-lift-presᵒ-≤v f)

    f[argmin]<v⁺ : ∀ {v} ⊤ xs → (f ⊤ < v) ⊎ (Any (λ x → f x < v) xs) →
                  f (argmin f ⊤ xs) < v
    f[argmin]<v⁺ = foldr-presᵒ (⊓-lift-presᵒ-<v f)
    
    v≤f[argmin]⁺ : ∀ {v ⊤ xs} → v ≤ f ⊤ → All (λ x → v ≤ f x) xs →
                  v ≤ f (argmin f ⊤ xs)
    v≤f[argmin]⁺ {v} = foldr-presᵇ (⊓-lift-presᵇ-v≤ f)

    v<f[argmin]⁺ : ∀ {v ⊤ xs} → v < f ⊤ → All (λ x → v < f x) xs →
                  v < f (argmin f ⊤ xs)
    v<f[argmin]⁺ {v} = foldr-presᵇ (⊓-lift-presᵇ-v< f)
    
    f[argmin]≤f[⊤] : ∀ ⊤ xs → f (argmin f ⊤ xs) ≤ f ⊤
    f[argmin]≤f[⊤] ⊤ xs = f[argmin]≤v⁺ ⊤ xs (inj₁ refl)

    postulate f[argmin]≤f[xs] : ∀ ⊤ xs → All (λ x → f (argmin f ⊤ xs) ≤ f x) xs
    --f[argmin]≤f[xs] ⊤ xs = {!!}

    f[argmin]≈f[v]⁺ : ∀ {v ⊤ xs} → v ∈ xs → All (λ x → f v ≤ f x) xs → f v ≤ f ⊤ →
                   f (argmin f ⊤ xs) ≈ f v
    f[argmin]≈f[v]⁺ v∈xs fv≤fxs fv≤f⊤ = antisym
      (f[argmin]≤v⁺ _ _ (inj₂ (lose v∈xs refl)))
      (v≤f[argmin]⁺ fv≤f⊤ fv≤fxs)

  module _ {a} {A : Set a} (f : A → B) where

    argmin-sel : ∀ ⊤ xs → (argmin f ⊤ xs ≡ ⊤) ⊎ (argmin f ⊤ xs ∈ xs)
    argmin-sel = foldr-selective (⊓-lift-sel f)

    argmin-all : ∀ {p} {P : Pred A p} {⊤ xs} →
                 P ⊤ → All P xs → P (argmin f ⊤ xs)
    argmin-all {P = P} {⊤} {xs} p⊤ pxs with argmin-sel ⊤ xs
    ... | inj₁ argmin≡⊤  = subst P (sym argmin≡⊤) p⊤
    ... | inj₂ argmin∈xs = lookup pxs argmin∈xs


    
    
    
    
    

  module _ {a} {A : Set a} where
  
    argmin[xs]<argmin[ys]⁺ : ∀ {f : A → B} {g : A → B} ⊤₁ {⊤₂} xs {ys : List A} →
                            (f ⊤₁ < g ⊤₂) ⊎ Any (λ x → f x < g ⊤₂) xs →
                            All (λ y → (f ⊤₁ < g y) ⊎ Any (λ x → f x < g y) xs) ys →
                            f (argmin f ⊤₁ xs) < g (argmin g ⊤₂ ys)
    argmin[xs]<argmin[ys]⁺ ⊤₁ xs xs<⊤₂ xs<ys =
      v<f[argmin]⁺ (f[argmin]<v⁺ ⊤₁ _ xs<⊤₂) (map (f[argmin]<v⁺ ⊤₁ xs) xs<ys)

    
    
{-
    min[xs]<min[ys]₁ : ∀ {xs ys ⊤₁ ⊤₂} → ⊤₁ < ⊤₂ → All (λ y → Any (_< y) xs) ys → min ⊤₁ xs < min ⊤₂ ys
    min[xs]<min[ys]₁ {xs} {[]}     {_}  {_}  ⊤₁<⊤₂ [] = <-transʳ (min[xs]≤⊤ _ xs) ⊤₁<⊤₂
    min[xs]<min[ys]₁ {xs} {y ∷ ys} {⊤₁} {⊤₂} ⊤₁<⊤₂ (xs<y  ∷ pxs) with ⊓-sel y (min ⊤₂ ys)
    ... | inj₁ y⊓m≡y rewrite y⊓m≡y = min[xs]<x ⊤₁ xs<y
    ... | inj₂ y⊓m≡m rewrite y⊓m≡m = min[xs]<min[ys]₁ ⊤₁<⊤₂ pxs
  -}
  
  ------------------------------------------------------------------------------
  -- Properties of argmax

  module _ {a} {A : Set a} {f : A → B} where
  {-
    f[argmax]≤v⁺ : ∀ {v} ⊤ xs → v ≤ f ⊤ → All (λ x → v ≤ f x) xs →
                  f (argmax f ⊤ xs) ≤ v
    f[argmax]≤v⁺ = foldr-presᵇ (⊔-lift-presᵒ-v≤ f)

    f[argmax]<v⁺ : ∀ {v} ⊤ xs → v < f ⊤ → All (λ x → v < f x) xs →
                  f (argmax f ⊤ xs) < v
    f[argmax]<v⁺ = foldr-presᵒ (⊓-lift-presᵒ-<v f)
    
    v≤f[argmax]⁺ : ∀ {v ⊤ xs} → (f ⊤ ≤ v) ⊎ (Any (λ x → f x ≤ v) xs) →
                  v ≤ f (argmax f ⊤ xs)
    v≤f[argmax]⁺ {v} = foldr-presᵒ (⊓-lift-presᵒ-≤v f)

    v<f[argmax]⁺ : ∀ {v ⊤ xs} → (f ⊤ < v) ⊎ (Any (λ x → f x < v) xs) →
                  v < f (argmax f ⊤ xs)
    v<f[argmax]⁺ {v} = foldr-presᵇ (⊓-lift-presᵇ-v< f)
    -}
  module _ {a} {A : Set a} {f : A → B} where

    argmax-sel : ∀ ⊤ xs → (argmax f ⊤ xs ≡ ⊤) ⊎ (argmax f ⊤ xs ∈ xs)
    argmax-sel = foldr-selective (⊔-lift-sel _)

    argmax-all : ∀ {p} {P : Pred A p} {⊤ xs} →
                 P ⊤ → All P xs → P (argmax f ⊤ xs)
    argmax-all {P = P} {⊤} {xs} p⊤ pxs with argmax-sel ⊤ xs
    ... | inj₁ argmax≡⊤  = subst P (sym argmax≡⊤) p⊤
    ... | inj₂ argmax∈xs = lookup pxs argmax∈xs


  ------------------------------------------------------------------------------
  -- Properties of min

  module _ {a} {A : Set a} where
  
    min≤v⁺ : ∀ {v} ⊤ xs → ⊤ ≤ v ⊎ Any (_≤ v) xs → min ⊤ xs ≤ v
    min≤v⁺ = f[argmin]≤v⁺

    min<v⁺ : ∀ {v} ⊤ xs → ⊤ < v ⊎ Any (_< v) xs → min ⊤ xs < v
    min<v⁺ = f[argmin]<v⁺

    v≤min⁺ : ∀ {v ⊤ xs} → v ≤ ⊤ → All (v ≤_) xs → v ≤ min ⊤ xs
    v≤min⁺ = v≤f[argmin]⁺

    v<min⁺ : ∀ {v ⊤ xs} → v < ⊤ → All (v <_) xs → v < min ⊤ xs
    v<min⁺ = v<f[argmin]⁺
     
    min⁺≈v : ∀ {v ⊤ xs} → v ∈ xs → All (v ≤_) xs → v ≤ ⊤ → min ⊤ xs ≈ v
    min⁺≈v = f[argmin]≈f[v]⁺

    min≤⊤ : ∀ ⊤ xs → min ⊤ xs ≤ ⊤
    min≤⊤ = f[argmin]≤f[⊤]
{-
    min[xs]∈xs : ∀ {⊤ xs} → min ⊤ xs ≢ ⊤ → min ⊤ xs ∈ xs
    min[xs]∈xs {⊤} {[]}     ⊤≢⊤ = contradiction refl ⊤≢⊤
    min[xs]∈xs {⊤} {x ∷ xs} m≢⊤ with ⊓-sel x (min ⊤ xs)
    ... | inj₁ y⊓m≡y rewrite y⊓m≡y = here refl
    ... | inj₂ y⊓m≡m rewrite y⊓m≡m = there (min[xs]∈xs m≢⊤)
  
    min[xs]<min[ys]₁ : ∀ {xs ys ⊤₁ ⊤₂} → ⊤₁ < ⊤₂ → All (λ y → Any (_< y) xs) ys → min ⊤₁ xs < min ⊤₂ ys
    min[xs]<min[ys]₁ {xs} {[]}     {_}  {_}  ⊤₁<⊤₂ [] = <-transʳ (min[xs]≤⊤ _ xs) ⊤₁<⊤₂
    min[xs]<min[ys]₁ {xs} {y ∷ ys} {⊤₁} {⊤₂} ⊤₁<⊤₂ (xs<y  ∷ pxs) with ⊓-sel y (min ⊤₂ ys)
    ... | inj₁ y⊓m≡y rewrite y⊓m≡y = min[xs]<x ⊤₁ xs<y
    ... | inj₂ y⊓m≡m rewrite y⊓m≡m = min[xs]<min[ys]₁ ⊤₁<⊤₂ pxs

    min[xs]<min[ys]₃ : ∀ {xs ys} ⊤₁ {⊤₂} → Any (_< ⊤₂) xs → All (λ y → Any (_< y) xs) ys → min ⊤₁ xs < min ⊤₂ ys
    min[xs]<min[ys]₃ {_} {[]}     ⊤₁ {⊤₂} xs<⊤₂ [] = min[xs]<x ⊤₁ xs<⊤₂
    min[xs]<min[ys]₃ {_} {y ∷ ys} ⊤₁ {⊤₂} xs<⊤₂ (xs<y ∷ pys) with ⊓-sel y (min ⊤₂ ys)
    ... | inj₁ y⊓m≡y rewrite y⊓m≡y = min[xs]<x ⊤₁ xs<y
    ... | inj₂ y⊓m≡m rewrite y⊓m≡m = min[xs]<min[ys]₃ ⊤₁ xs<⊤₂ pys
-}

  ------------------------------------------------------------------------------
  -- Properties of max

  postulate max≤v⁺ : ∀ {v xs ⊥} → All (_≤ v) xs → ⊥ ≤ v → max ⊥ xs ≤ v
  -- max[xs]≤v⁺ = {!f[argmax]≤v ?!}

  postulate max<v⁺ : ∀ {v xs ⊥} → All (_< v) xs → ⊥ < v → max ⊥ xs < v
  -- ymax[xs]<v⁺ = {!!}
  
  postulate v≤max⁺ : ∀ {v xs} ⊥ → Any (v ≤_) xs → v ≤ max ⊥ xs
  -- v≤max[xs]⁺ = {!!}
  
  postulate v<max⁺ : ∀ {v xs} ⊥ → Any (v <_) xs → v < max ⊥ xs
  -- v<max[xs]⁺ = {!!}
  
  postulate ⊥≤max : ∀ ⊥ xs → ⊥ ≤ max ⊥ xs
  -- ⊥≤max[xs] = {!!}

  postulate max≤max⁺ : ∀ ⊥₁ {⊥₂} {xs} {ys} → ⊥₁ ≤ ⊥₂ ⊎ Any (⊥₁ ≤_) ys →
                       All (λ x → x ≤ ⊥₂ ⊎ Any (x ≤_) ys) xs → max ⊥₁ xs ≤ max ⊥₂ ys
                
  postulate max-mono-⊆ : ∀ {⊥₁} {⊥₂} {xs ys} → ⊥₁ ≤ ⊥₂ → xs ⊆ ys → max ⊥₁ xs ≤ max ⊥₂ ys

  


{-


    min[xs]∈xs : ∀ {⊤ xs} → min ⊤ xs ≢ ⊤ → min ⊤ xs ∈ xs
    min[xs]∈xs {⊤} {[]}     ⊤≢⊤ = contradiction refl ⊤≢⊤
    min[xs]∈xs {⊤} {x ∷ xs} m≢⊤ with ⊓-sel x (min ⊤ xs)
    ... | inj₁ y⊓m≡y rewrite y⊓m≡y = here refl
    ... | inj₂ y⊓m≡m rewrite y⊓m≡m = there (min[xs]∈xs m≢⊤)
-}
