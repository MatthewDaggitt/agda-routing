open import Algebra.FunctionProperties using (Op₂; RightIdentity; Selective)
open import Relation.Binary
  using (Setoid; Rel; Symmetric; _Respects_; _Preserves_⟶_; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality
  using (refl; _≡_; _≢_; cong; subst; subst₂; inspect; [_])
open import Data.List.Relation.Binary.Pointwise as Pointwise using ([]; _∷_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary using (¬_; yes; no)
open import Function using (_∘_; id)
open import Data.List.All using (All; _∷_; [])
open import Data.List.All.Properties using (All¬⇒¬Any)
open import Data.List.Any using (index)
import Data.List.Membership.Setoid as Membership
open import Data.List.Membership.Setoid.Properties
open import Data.Nat using (_≤_; _<_; zero; suc; s≤s; z≤n)
open import Data.Fin using (Fin; suc)
open import Data.List hiding (any)
open import Data.List.Any using (here; there; any) renaming (map to mapₐ)
open import Data.Product using (∃; ∃₂; _×_; _,_; swap; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (Level)
open import Relation.Unary using (Decidable; _⇒_) renaming (_⊆_ to _⋐_)

open import RoutingLib.Data.List
open import RoutingLib.Data.List.Relation.Unary.Any.Properties
open import Data.List.Relation.Unary.Unique.Setoid using (Unique; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)


module RoutingLib.Data.List.Membership.Setoid.Properties where

private
  variable
    a b c p ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    
-----------------------------------
-- Properties involving 1 setoid --
-----------------------------------

module _ (S : Setoid c ℓ) where

  open Setoid S renaming (Carrier to A; refl to ≈-refl)
  open Setoid (Pointwise.setoid S) using () renaming (_≈_ to _≈ₗ_; sym to symₗ; refl to reflₗ)

  open Membership S using (_∈_; _∉_)
  open Membership (Pointwise.setoid S) using () renaming (_∈_ to _∈ₗ_)


  ∉-filter₁ : ∀ {P : A → Set p} (P? : Decidable P) {v} {xs} → v ∉ xs → v ∉ filter P? xs
  ∉-filter₁ P? {v} {x ∷ xs} v∉x∷xs v∈f[x∷xs] with P? x | v∈f[x∷xs]
  ... | no  _ | v∈f[xs]       = ∉-filter₁ P? (v∉x∷xs ∘ there) v∈f[xs]
  ... | yes _ | here  v≈x     = v∉x∷xs (here v≈x)
  ... | yes _ | there v∈f[xs] = ∉-filter₁ P? (v∉x∷xs ∘ there) v∈f[xs]

  ∉-filter₂ : ∀ {P : A → Set p} (P? : Decidable P) → P Respects _≈_ → ∀ {v} → ¬ P v → ∀ xs → v ∉ filter P? xs
  ∉-filter₂ P? resp ¬Pv (x ∷ xs) v∈f[x∷xs] with P? x | v∈f[x∷xs]
  ... | no  _  | v∈f[xs]       = ∉-filter₂ P? resp ¬Pv xs v∈f[xs]
  ... | yes Px | here  v≈x     = ¬Pv (resp (sym v≈x) Px)
  ... | yes _  | there v∈f[xs] = ∉-filter₂ P? resp ¬Pv xs v∈f[xs]

  index-cong : ∀ {x y xs} → (x∈xs : x ∈ xs) (y∈xs : y ∈ xs) → Unique S xs → x ≈ y → index x∈xs ≡ index y∈xs
  index-cong (here x≈z)   (here y≈z)   _            x≈y = refl
  index-cong (here x≈z)   (there y∈xs) (z≉xs ∷ xs!) x≈y = contradiction (∈-resp-≈ S (trans (sym x≈y) x≈z) y∈xs) (All¬⇒¬Any z≉xs)
  index-cong (there x∈xs) (here y≈z)   (z≉xs ∷ xs!) x≈y = contradiction (∈-resp-≈ S (trans x≈y y≈z) x∈xs) (All¬⇒¬Any z≉xs)
  index-cong (there x∈xs) (there y∈xs) (_ ∷ xs!)    x≈y = cong suc (index-cong x∈xs y∈xs xs! x≈y)


------------------------------------
-- Properties involving 3 setoids --
------------------------------------

module _ (S₁ : Setoid a ℓ₁) (S₂ : Setoid b ℓ₂) (S₃ : Setoid c ℓ₃) where

  open Setoid S₁ using () renaming (_≈_ to _≈₁_; refl to refl₁; sym to sym₁)
  open Setoid S₂ using () renaming (_≈_ to _≈₂_; refl to refl₂; sym to sym₂)
  open Setoid S₃ using () renaming (_≈_ to _≈₃_; refl to refl₃; sym to sym₃)
  open Membership S₁ using () renaming (_∈_ to _∈₁_)
  open Membership S₂ using () renaming (_∈_ to _∈₂_)
  open Membership S₃ using () renaming (_∈_ to _∈₃_)

  -- combine

  ∈-combine⁺ : ∀ {f} → f Preserves₂ _≈₁_ ⟶ _≈₂_ ⟶ _≈₃_ →
               ∀ {xs ys a b} → a ∈₁ xs → b ∈₂ ys → f a b ∈₃ combine f xs ys
  ∈-combine⁺ pres {_ ∷ _} (here  a≈x)  b∈ys = ∈-resp-≈ S₃ (pres (sym₁ a≈x) refl₂) (∈-++⁺ˡ S₃ (∈-map⁺ S₂ S₃ (pres refl₁) b∈ys))
  ∈-combine⁺ pres {_ ∷ _} (there a∈xs) b∈ys = ∈-++⁺ʳ S₃ _ (∈-combine⁺ pres a∈xs b∈ys)

  ∈-combine⁻ : ∀ f xs ys {v} → v ∈₃ combine f xs ys →
               ∃₂ λ a b → a ∈₁ xs × b ∈₂ ys × v ≈₃ f a b
  ∈-combine⁻ f (x ∷ xs) ys v∈map++com with ∈-++⁻ S₃ (map (f x) ys) v∈map++com
  ∈-combine⁻ f (x ∷ xs) ys v∈map++com | inj₁ v∈map with ∈-map⁻ S₂ S₃ v∈map
  ... | (b , b∈ys , v≈fxb) = x , b , here refl₁ , b∈ys , v≈fxb
  ∈-combine⁻ f (x ∷ xs) ys v∈map++com | inj₂ v∈com with ∈-combine⁻ f xs ys v∈com
  ... | (a , b , a∈xs , b∈ys , v≈fab) = a , b , there a∈xs , b∈ys , v≈fab



module _ (S₁ : Setoid a ℓ₁) (S₂ : Setoid b ℓ₂) where

  open Setoid S₁ using () renaming (sym to sym₁)
  open Setoid S₂ using () renaming (sym to sym₂)
  open Membership S₁ using () renaming (_∈_ to _∈₁_)
  open Membership S₂ using () renaming (_∈_ to _∈₂_)
  open Membership (S₁ ×ₛ S₂) using () renaming (_∈_ to _∈ₓ_)

  ∈-allPairs⁺ : ∀ {x y xs ys} → x ∈₁ xs → y ∈₂ ys → (x , y) ∈ₓ allPairs xs ys
  ∈-allPairs⁺ = ∈-combine⁺ S₁ S₂ (S₁ ×ₛ S₂) _,_

  ∈-allPairs⁻ : ∀ {xy} xs ys → xy ∈ₓ allPairs xs ys → proj₁ xy ∈₁ xs × proj₂ xy ∈₂ ys
  ∈-allPairs⁻ {xy} xs ys xs∈xsys with ∈-combine⁻ S₁ S₂ (S₁ ×ₛ S₂) _,_ xs ys xs∈xsys
  ... | (x , y , x∈xs , y∈ys , x≈x , y≈y) = ∈-resp-≈ S₁ (sym₁ x≈x) x∈xs , ∈-resp-≈ S₂ (sym₂ y≈y) y∈ys
