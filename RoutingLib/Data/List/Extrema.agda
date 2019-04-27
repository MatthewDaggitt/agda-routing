open import Algebra.FunctionProperties
import Algebra.Construct.NaturalChoice.Min as Min
import Algebra.Construct.NaturalChoice.Max as Max
open import Data.List using (List; foldr)
open import Data.List.Any as Any using (Any; here; there)
open import Data.List.All using (All; []; _∷_; lookup; map; tabulate)
open import Data.List.Membership.Propositional using (_∈_; lose)
open import Data.List.Relation.Subset.Propositional using (_⊆_)
open import Data.List.Properties using ()
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (id; flip; _on_)
open import Level using (Level)
open import Relation.Unary using (Pred)
open import Relation.Binary using (TotalOrder; Setoid)
import Relation.Binary.Construct.NonStrictToStrict as NonStrictToStrict
open import Relation.Binary.PropositionalEquality
  using (_≡_; sym; subst) renaming (refl to ≡-refl)
import Relation.Binary.Construct.On as On

open import RoutingLib.Data.List.Properties
open import RoutingLib.Algebra.Construct.Lifting
open import Data.List.Membership.Propositional.Properties
  using (foldr-selective)

module RoutingLib.Data.List.Extrema
  {b ℓ₁ ℓ₂} (totalOrder : TotalOrder b ℓ₁ ℓ₂) where

------------------------------------------------------------------------------
-- Setup

open TotalOrder totalOrder renaming (Carrier to B)
open NonStrictToStrict _≈_ _≤_ using (_<_)
open import RoutingLib.Data.List.Extrema.Core totalOrder

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------------
-- Functions

argmin : (f : A → B) → A → List A → A
argmin f = foldr (⊓-lift f)

argmax : (f : A → B) → A → List A → A
argmax f = foldr (⊔-lift f)

min : B → List B → B
min = argmin id

max : B → List B → B
max = argmax id

------------------------------------------------------------------------------
-- Properties of argmin

module _ {f : A → B} where

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

  f[argmin]≤f[xs] : ∀ ⊤ xs → All (λ x → f (argmin f ⊤ xs) ≤ f x) xs
  f[argmin]≤f[xs] ⊤ xs = foldr-forcesᵇ (⊓-lift-forcesᵇ-v≤ f) ⊤ xs refl

  f[argmin]≈f[v]⁺ : ∀ {v ⊤ xs} → v ∈ xs → All (λ x → f v ≤ f x) xs → f v ≤ f ⊤ →
                 f (argmin f ⊤ xs) ≈ f v
  f[argmin]≈f[v]⁺ v∈xs fv≤fxs fv≤f⊤ = antisym
    (f[argmin]≤v⁺ _ _ (inj₂ (lose v∈xs refl)))
    (v≤f[argmin]⁺ fv≤f⊤ fv≤fxs)

module _ (f : A → B) where

  argmin-sel : ∀ ⊤ xs → (argmin f ⊤ xs ≡ ⊤) ⊎ (argmin f ⊤ xs ∈ xs)
  argmin-sel = foldr-selective (⊓-lift-sel f)

  argmin-all : ∀ {p} {P : Pred A p} {⊤ xs} →
               P ⊤ → All P xs → P (argmin f ⊤ xs)
  argmin-all {P = P} {⊤} {xs} p⊤ pxs with argmin-sel ⊤ xs
  ... | inj₁ argmin≡⊤  = subst P (sym argmin≡⊤) p⊤
  ... | inj₂ argmin∈xs = lookup pxs argmin∈xs

argmin[xs]<argmin[ys]⁺ : ∀ {f : A → B} {g : A → B} ⊤₁ {⊤₂} xs {ys : List A} →
                        (f ⊤₁ < g ⊤₂) ⊎ Any (λ x → f x < g ⊤₂) xs →
                        All (λ y → (f ⊤₁ < g y) ⊎ Any (λ x → f x < g y) xs) ys →
                        f (argmin f ⊤₁ xs) < g (argmin g ⊤₂ ys)
argmin[xs]<argmin[ys]⁺ ⊤₁ xs xs<⊤₂ xs<ys =
  v<f[argmin]⁺ (f[argmin]<v⁺ ⊤₁ _ xs<⊤₂) (map (f[argmin]<v⁺ ⊤₁ xs) xs<ys)

------------------------------------------------------------------------------
-- Properties of argmax

module _ {f : A → B} where

  f[argmax]≤v⁺ : ∀ {v ⊥ xs} → f ⊥ ≤ v → All (λ x → f x ≤ v) xs →
                f (argmax f ⊥ xs) ≤ v
  f[argmax]≤v⁺ = foldr-presᵇ (⊔-lift-presᵇ-≤v f)

  f[argmax]<v⁺ : ∀ {v ⊥ xs} → f ⊥ < v → All (λ x → f x < v) xs →
                f (argmax f ⊥ xs) < v
  f[argmax]<v⁺ = foldr-presᵇ (⊔-lift-presᵇ-<v f)

  v≤f[argmax]⁺ : ∀ {v} ⊥ xs → (v ≤ f ⊥) ⊎ (Any (λ x → v ≤ f x) xs) →
                v ≤ f (argmax f ⊥ xs)
  v≤f[argmax]⁺ = foldr-presᵒ (⊔-lift-presᵒ-v≤ f)

  v<f[argmax]⁺ : ∀ {v} ⊥ xs → (v < f ⊥) ⊎ (Any (λ x → v < f x) xs) →
                v < f (argmax f ⊥ xs)
  v<f[argmax]⁺ = foldr-presᵒ (⊔-lift-presᵒ-v< f)

  f[⊥]≤f[argmax] : ∀ ⊥ xs → f ⊥ ≤ f (argmax f ⊥ xs)
  f[⊥]≤f[argmax] ⊥ xs = v≤f[argmax]⁺ ⊥ xs (inj₁ refl)

  f[xs]≤f[argmax] : ∀ ⊥ xs → All (λ x → f x ≤ f (argmax f ⊥ xs)) xs
  f[xs]≤f[argmax] ⊥ xs = foldr-forcesᵇ (⊔-lift-forcesᵇ-≤v f) ⊥ xs refl

module _ {f : A → B} where

  argmax-sel : ∀ ⊥ xs → (argmax f ⊥ xs ≡ ⊥) ⊎ (argmax f ⊥ xs ∈ xs)
  argmax-sel = foldr-selective (⊔-lift-sel _)

  argmax-all : ∀ {p} {P : Pred A p} {⊥ xs} →
               P ⊥ → All P xs → P (argmax f ⊥ xs)
  argmax-all {P = P} {⊥} {xs} p⊥ pxs with argmax-sel ⊥ xs
  ... | inj₁ argmax≡⊥  = subst P (sym argmax≡⊥) p⊥
  ... | inj₂ argmax∈xs = lookup pxs argmax∈xs

module _ {f g : A → B} where

  argmax≤argmax⁺ : ∀ {⊥₁} ⊥₂ {xs : List A} ys →
                   (f ⊥₁ ≤ g ⊥₂) ⊎ Any (λ y → f ⊥₁ ≤ g y) ys →
                   All (λ x → (f x ≤ g ⊥₂) ⊎ Any (λ y → f x ≤ g y) ys) xs →
                   f (argmax f ⊥₁ xs) ≤ g (argmax g ⊥₂ ys)
  argmax≤argmax⁺ ⊥₂ ys ⊥₁≤ys xs≤ys =
    f[argmax]≤v⁺ (v≤f[argmax]⁺ ⊥₂ _ ⊥₁≤ys) (map (v≤f[argmax]⁺ ⊥₂ ys) xs≤ys)

  argmax<argmax⁺ : ∀ {⊥₁} ⊥₂ {xs : List A} ys →
                   (f ⊥₁ < g ⊥₂) ⊎ Any (λ y → f ⊥₁ < g y) ys →
                   All (λ x → (f x < g ⊥₂) ⊎ Any (λ y → f x < g y) ys) xs →
                   f (argmax f ⊥₁ xs) < g (argmax g ⊥₂ ys)
  argmax<argmax⁺ ⊥₂ ys ⊥₁<ys xs<ys =
    f[argmax]<v⁺ (v<f[argmax]⁺ ⊥₂ _ ⊥₁<ys) (map (v<f[argmax]⁺ ⊥₂ ys) xs<ys)

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

------------------------------------------------------------------------------
-- Properties of max

max≤v⁺ : ∀ {v ⊥ xs} → ⊥ ≤ v → All (_≤ v) xs → max ⊥ xs ≤ v
max≤v⁺ = f[argmax]≤v⁺

max<v⁺ : ∀ {v xs ⊥} → ⊥ < v → All (_< v) xs → max ⊥ xs < v
max<v⁺ = f[argmax]<v⁺

v≤max⁺ : ∀ {v} ⊥ xs → v ≤ ⊥ ⊎ Any (v ≤_) xs → v ≤ max ⊥ xs
v≤max⁺ = v≤f[argmax]⁺

v<max⁺ : ∀ {v} ⊥ xs → v < ⊥ ⊎ Any (v <_) xs → v < max ⊥ xs
v<max⁺ = v<f[argmax]⁺

⊥≤max : ∀ ⊥ xs → ⊥ ≤ max ⊥ xs
⊥≤max = f[⊥]≤f[argmax]

xs≤max : ∀ ⊥ xs → All (_≤ max ⊥ xs) xs
xs≤max = f[xs]≤f[argmax]

max≤max⁺ : ∀ {⊥₁} ⊥₂ {xs} ys → ⊥₁ ≤ ⊥₂ ⊎ Any (⊥₁ ≤_) ys →
           All (λ x → x ≤ ⊥₂ ⊎ Any (x ≤_) ys) xs → max ⊥₁ xs ≤ max ⊥₂ ys
max≤max⁺ = argmax≤argmax⁺

max-mono-⊆ : ∀ {⊥₁} {⊥₂} {xs ys} → ⊥₁ ≤ ⊥₂ → xs ⊆ ys → max ⊥₁ xs ≤ max ⊥₂ ys
max-mono-⊆ {⊥₁} {⊥₂} {xs} {ys} ⊥₁≤⊥₂ xs⊆ys = max≤max⁺ {⊥₁} ⊥₂ {xs} ys (inj₁ ⊥₁≤⊥₂) (tabulate λ x∈xs → inj₂ (Any.map (λ {≡-refl → refl}) (xs⊆ys x∈xs)))
