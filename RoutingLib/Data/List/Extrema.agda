open import Algebra.FunctionProperties
open import Data.List using (List; foldr)
open import Data.List.Any using (Any; here; there)
open import Data.List.All using (All; []; _∷_; lookup; map)
open import Data.List.Any.Membership.Propositional using (_∈_; lose)
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
open import RoutingLib.Data.List.Membership.Propositional.Properties using (foldr-∈)

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

    f[argmin]≤v : ∀ {v} ⊤ xs → (f ⊤ ≤ v) ⊎ (Any (λ x → f x ≤ v) xs) →
                  f (argmin f ⊤ xs) ≤ v
    f[argmin]≤v = foldr-presᵒ ⊓-lift-presᵒ-≤v
    
    f[argmin]<v : ∀ {v} ⊤ xs → (f ⊤ < v) ⊎ (Any (λ x → f x < v) xs) →
                  f (argmin f ⊤ xs) < v
    f[argmin]<v = foldr-presᵒ ⊓-lift-presᵒ-<v

    v≤f[argmin] : ∀ {v ⊤ xs} → v ≤ f ⊤ → All (λ x → v ≤ f x) xs →
                  v ≤ f (argmin f ⊤ xs)
    v≤f[argmin] {v} = foldr-presᵇ (⊓-lift-presᵇ-v≤ f)

    v<f[argmin] : ∀ {v ⊤ xs} → v < f ⊤ → All (λ x → v < f x) xs →
                  v < f (argmin f ⊤ xs)
    v<f[argmin] {v} = foldr-presᵇ (⊓-lift-presᵇ-v< f)



    f[argmin]≤f[⊤] : ∀ ⊤ xs → f (argmin f ⊤ xs) ≤ f ⊤
    f[argmin]≤f[⊤] ⊤ xs = f[argmin]≤v ⊤ xs (inj₁ refl)

    f[argmin]≈fv : ∀ {v ⊤ xs} → v ∈ xs → All (λ x → f v ≤ f x) xs → f v ≤ f ⊤ →
                   f (argmin f ⊤ xs) ≈ f v
    f[argmin]≈fv v∈xs fv≤fxs fv≤f⊤ = antisym
      (f[argmin]≤v _ _ (inj₂ (lose v∈xs refl)))
      (v≤f[argmin] fv≤f⊤ fv≤fxs)
    
    argmin-sel : ∀ ⊤ xs → (argmin f ⊤ xs ≡ ⊤) ⊎ (argmin f ⊤ xs ∈ xs)
    argmin-sel = foldr-∈ (⊓-lift-sel f)

    argmin-all : ∀ {p} {P : Pred A p} {⊤ xs} →
                 P ⊤ → All P xs → P (argmin f ⊤ xs)
    argmin-all {P = P} {⊤} {xs} p⊤ pxs with argmin-sel ⊤ xs
    ... | inj₁ argmin≡⊤  = subst P (sym argmin≡⊤) p⊤
    ... | inj₂ argmin∈xs = lookup pxs argmin∈xs


    argmin[xs]<argmin[ys] : ∀ {xs ys : List A} ⊤₁ {⊤₂} →
                            f ⊤₁ < f ⊤₂ ⊎ Any (λ x → f x < f ⊤₂) xs →
                            All (λ y → Any (λ x → f x < f y) xs) ys →
                            f (argmin f ⊤₁ xs) < f (argmin f ⊤₂ ys)
    argmin[xs]<argmin[ys] ⊤₁ xs<⊤₂ xs<ys =
      v<f[argmin] (f[argmin]<v ⊤₁ _ xs<⊤₂) (map (f[argmin]<v ⊤₁ _) {!!})
    
{-
    min[xs]<min[ys]₁ : ∀ {xs ys ⊤₁ ⊤₂} → ⊤₁ < ⊤₂ → All (λ y → Any (_< y) xs) ys → min ⊤₁ xs < min ⊤₂ ys
    min[xs]<min[ys]₁ {xs} {[]}     {_}  {_}  ⊤₁<⊤₂ [] = <-transʳ (min[xs]≤⊤ _ xs) ⊤₁<⊤₂
    min[xs]<min[ys]₁ {xs} {y ∷ ys} {⊤₁} {⊤₂} ⊤₁<⊤₂ (xs<y  ∷ pxs) with ⊓-sel y (min ⊤₂ ys)
    ... | inj₁ y⊓m≡y rewrite y⊓m≡y = min[xs]<x ⊤₁ xs<y
    ... | inj₂ y⊓m≡m rewrite y⊓m≡m = min[xs]<min[ys]₁ ⊤₁<⊤₂ pxs

    

    postulate f[argmin]≤x⁺ : ∀ {x} ⊤ xs  →
                             Any (λ y → f y ≤ x) xs ⊎ (f ⊤ ≤ x) →
                             f (argmin f ⊤ xs) ≤ x
    {-
    f[argmin]≤x⁺ {x} ⊤ xs (inj₁ xs≤x) = foldr-presᵒ {!!} ⊤ xs≤x  --n≤m⊎o≤m⇒n⊓o≤m
    f[argmin]≤x⁺ {x} ⊤ xs (inj₂ ⊤≤x)  = foldr-presʳ {P = λ y → f y ≤ x} {!!} xs ⊤≤x
    -}

    postulate f[argmin]≤fxs : ∀ ⊤ xs → All (λ x → f (argmin f ⊤ xs) ≤ f x) xs
    -- f[argmin]≤fxs ⊤ xs = {!!}

    
  {-
    f[argmin]≤x⁻ : ∀ {f x xs} ⊤ →
                     argmin f ⊤ xs ≤ x →
                     Any (λ y → f y ≤ x) xs ⊎ (f ⊤ ≤ x)
    f[argmin]≤x⁻ = {!!}
    
    argmin[xs]≤f⊤ : ∀ {f} ⊤ xs → argmin f ⊤ xs ≤ f ⊤
    argmin[xs]≤f⊤ ⊤ xs = foldr-presʳ {!!} xs refl

    x≤argmin[xs] : ∀ {x xs ⊤} → All (x ≤_) xs → x ≤ ⊤ → x ≤ min ⊤ xs
    x≤argmin[xs] = foldr-presᵇ {!!} --m≤n×m≤o⇒m≤n⊓o

  argmin[xs]<x : ∀ {x xs} ⊤ → Any (_< x) xs → min ⊤ xs < x
  argmin[xs]<x = foldr-⊎pres n<m⊎o<m⇒n⊓o<m
  
  x<argmin[xs] : ∀ {x xs ⊤} → All (x <_) xs → x < ⊤ → x < min ⊤ xs
  x<argmin[xs] = foldr-×pres m≤n×m≤o⇒m≤n⊓o
  -}
  -}
  
  ------------------------------------------------------------------------------
  -- Properties of argmax
  
  module _ {a} {A : Set a} {f : A → B} where

    argmax-sel : ∀ ⊤ xs → (argmax f ⊤ xs ≡ ⊤) ⊎ (argmax f ⊤ xs ∈ xs)
    argmax-sel = foldr-∈ (⊔-lift-sel _)

    argmax-all : ∀ {p} {P : Pred A p} {⊤ xs} →
                 P ⊤ → All P xs → P (argmax f ⊤ xs)
    argmax-all {P = P} {⊤} {xs} p⊤ pxs with argmax-sel ⊤ xs
    ... | inj₁ argmax≡⊤  = subst P (sym argmax≡⊤) p⊤
    ... | inj₂ argmax∈xs = lookup pxs argmax∈xs


  ------------------------------------------------------------------------------
  -- Properties of min

  module _ {a} {A : Set a} where
  
    min≤v : ∀ {v} ⊤ xs → ⊤ ≤ v ⊎ Any (_≤ v) xs → min ⊤ xs ≤ v
    min≤v = f[argmin]≤v

    min<v : ∀ {v} ⊤ xs → ⊤ < v ⊎ Any (_< v) xs → min ⊤ xs < v
    min<v = f[argmin]<v

    v≤min : ∀ {v ⊤ xs} → v ≤ ⊤ → All (v ≤_) xs → v ≤ min ⊤ xs
    v≤min = v≤f[argmin]

    v<min : ∀ {v ⊤ xs} → v < ⊤ → All (v <_) xs → v < min ⊤ xs
    v<min = v<f[argmin]
     
    min≈v : ∀ {v ⊤ xs} → v ∈ xs → All (v ≤_) xs → v ≤ ⊤ → min ⊤ xs ≈ v
    min≈v = f[argmin]≈fv

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
  
  ------------------------------------------------------------------------------
  -- Properties of max

  max[xs]≤x : ∀ {x xs ⊥} → All (_≤ x) xs → ⊥ ≤ x → max ⊥ xs ≤ x
  max[xs]≤x = foldr-presᵇ n≤m×o≤m⇒n⊔o≤m

  max[xs]<x : ∀ {x xs ⊥} → All (_< x) xs → ⊥ < x → max ⊥ xs < x
  max[xs]<x = foldr-presᵇ n≤m×o≤m⇒n⊔o≤m

  x≤max[xs] : ∀ {x xs} ⊥ → Any (x ≤_) xs → x ≤ max ⊥ xs
  x≤max[xs] = foldr-presᵒ m≤n⊎m≤o⇒m≤n⊔o
  
  x<max[xs] : ∀ {x xs} ⊥ → Any (x <_) xs → x < max ⊥ xs
  x<max[xs] = foldr-presᵒ m≤n⊎m≤o⇒m≤n⊔o

  ⊥≤max[xs] : ∀ ⊥ xs → ⊥ ≤ max ⊥ xs
  ⊥≤max[xs] ⊥ xs = foldr-presʳ m≤o⇒m≤n⊔o xs ≤-refl
  
  max[xs]≡x : ∀ {x xs ⊥} → x ∈ xs → All (_≤ x) xs → ⊥ ≤ x → max ⊥ xs ≡ x
  max[xs]≡x x∈xs xs≤x ⊥≤x = ≤-antisym (max[xs]≤x xs≤x ⊥≤x) (x≤max[xs] _ (lose x∈xs ≤-refl))
  
  max[xs]∈xs : ∀ {⊥ xs} → max ⊥ xs ≢ ⊥ → max ⊥ xs ∈ xs
  max[xs]∈xs {⊥} {[]}     ⊥≢⊥ = contradiction refl ⊥≢⊥
  max[xs]∈xs {⊥} {x ∷ xs} m≢⊥ with ⊔-sel x (max ⊥ xs)
  ... | inj₁ x⊔r≡x rewrite x⊔r≡x = here refl
  ... | inj₂ x⊔r≡r rewrite x⊔r≡r = there (max[xs]∈xs m≢⊥)

-}





{-


    min[xs]∈xs : ∀ {⊤ xs} → min ⊤ xs ≢ ⊤ → min ⊤ xs ∈ xs
    min[xs]∈xs {⊤} {[]}     ⊤≢⊤ = contradiction refl ⊤≢⊤
    min[xs]∈xs {⊤} {x ∷ xs} m≢⊤ with ⊓-sel x (min ⊤ xs)
    ... | inj₁ y⊓m≡y rewrite y⊓m≡y = here refl
    ... | inj₂ y⊓m≡m rewrite y⊓m≡m = there (min[xs]∈xs m≢⊤)
-}
