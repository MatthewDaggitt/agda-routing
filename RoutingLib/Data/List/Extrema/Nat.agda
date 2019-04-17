open import Data.Nat using (ℕ; _≤_; _<_)
open import Data.Nat.Properties using (≤-totalOrder; ≤∧≢⇒<; <⇒≤; <⇒≢)
open import Data.Sum as Sum using (_⊎_)
open import Data.List using (List)
open import Data.List.Any as Any using (Any)
open import Data.List.All as All using (All)
open import Data.Product using (_×_; _,_; uncurry′)
open import Relation.Binary.PropositionalEquality using (_≢_)

import RoutingLib.Data.List.Extrema as ExtremaGen

module RoutingLib.Data.List.Extrema.Nat where

  module Extrema = ExtremaGen ≤-totalOrder

  private
    <⇒<× : ∀ {x y} → x < y → x ≤ y × x ≢ y
    <⇒<× x<y = <⇒≤ x<y , <⇒≢ x<y

    <×⇒< : ∀ {x y} → x ≤ y × x ≢ y → x < y
    <×⇒< (x≤y , x≢y) = ≤∧≢⇒< x≤y x≢y

  open Extrema public hiding (f[argmin]<v⁺; v<f[argmin]⁺; argmin[xs]<argmin[ys]⁺)

  module _ {a} {A : Set a} {f : A → ℕ} where

    f[argmin]<v : ∀ {v} ⊤ xs → (f ⊤ < v) ⊎ (Any (λ x → f x < v) xs) →
                  f (argmin f ⊤ xs) < v
    f[argmin]<v ⊤ xs arg =
      <×⇒< (Extrema.f[argmin]<v⁺ ⊤ xs (Sum.map <⇒<× (Any.map <⇒<×) arg))

    v<f[argmin] : ∀ {v ⊤ xs} → v < f ⊤ → All (λ x → v < f x) xs →
                  v < f (argmin f ⊤ xs)
    v<f[argmin] {v} v<f⊤ v<fxs = <×⇒< (Extrema.v<f[argmin]⁺ (<⇒<× v<f⊤) (All.map <⇒<× v<fxs))


  module _ {a} {A : Set a} {f : A → ℕ} {g : A → ℕ} where

    argmin[xs]<argmin[ys] : ∀ ⊤₁ {⊤₂} xs {ys : List A} →
                            (f ⊤₁ < g ⊤₂) ⊎ Any (λ x → f x < g ⊤₂) xs →
                            All (λ y → (f ⊤₁ < g y) ⊎ Any (λ x → f x < g y) xs) ys →
                            f (argmin f ⊤₁ xs) < g (argmin g ⊤₂ ys)
    argmin[xs]<argmin[ys] ⊤₁ xs xs<⊤₂ xs<ys =
      v<f[argmin] (f[argmin]<v ⊤₁ _ xs<⊤₂) (All.map (f[argmin]<v ⊤₁ xs) xs<ys)
