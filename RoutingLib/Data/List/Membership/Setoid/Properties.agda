open import Level using (_⊔_)
open import Relation.Binary using (Setoid; Rel; Symmetric; _Respects_; _Preserves_⟶_; _Preserves₂_⟶_⟶_) renaming (Decidable to Decidable₂)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_; cong; subst; subst₂; inspect; [_]) renaming (trans to ≡-trans; sym to ≡-sym; setoid to ≡-setoid)
open import Relation.Binary.List.Pointwise using ([]; _∷_) renaming (setoid to list-setoid)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary using (¬_; yes; no)
open import Function using (_∘_; id)
open import Data.List.All using (All; _∷_; [])
open import Data.List.All.Properties using (All¬⇒¬Any)
open import Data.List.Any using (index)
open import Data.Nat using (_≤_; _<_; zero; suc; s≤s; z≤n)
open import Data.Nat.Properties using (suc-injective; <⇒≤; ≤-trans; n≤1+n)
open import Data.Fin using (Fin)
open import Data.Maybe using (nothing; just; Maybe; Eq; Eq-refl; Eq-sym; Eq-trans; drop-just; just-injective)
open import Data.Empty using (⊥-elim)
open import Data.List hiding (any)
open import Data.List.Any using (here; there; any) renaming (map to mapₐ)
open import Data.List.Relation.Permutation.Inductive using (_↭_)
open import Data.Product using (∃; ∃₂; _×_; _,_; swap)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Unary using (Decidable; _⇒_) renaming (_⊆_ to _⋐_)
open import Algebra.FunctionProperties using (Op₂; RightIdentity; Selective)

open import RoutingLib.Data.List
open import RoutingLib.Data.Maybe using (Eq-reflexive)
import RoutingLib.Data.List.Membership.Setoid as Membership
open import RoutingLib.Data.List.Any.Properties
open import RoutingLib.Data.List.Uniqueness.Setoid using (Unique; _∷_)
open import RoutingLib.Data.List.AllPairs using ([]; _∷_)


module RoutingLib.Data.List.Membership.Setoid.Properties where

  -----------------------------------
  -- Properties involving 1 setoid --
  -----------------------------------

  module _ {c ℓ} (S : Setoid c ℓ) where

    open Setoid S renaming (Carrier to A; refl to ≈-refl)
    open Setoid (list-setoid S) using () renaming (_≈_ to _≈ₗ_; sym to symₗ; refl to reflₗ)

    open import Data.List.Membership.Setoid S using (_∈_; _∉_)
    open import Data.List.Membership.Setoid.Properties
    open import Data.List.Membership.Setoid (list-setoid S) using () renaming (_∈_ to _∈ₗ_)

    {-
    ∈-applyBetween⁺ : ∀ f {s e i} → s ≤ i → i < e → f i ∈ applyBetween f s e
    ∈-applyBetween⁺ f s≤i i<e = Any-applyBetween⁺ f s≤i i<e ≈-refl

    ∈-applyBetween⁻ : ∀ f s e {v} → v ∈ applyBetween f s e → ∃ λ i → s ≤ i × i < e × v ≈ f i
    ∈-applyBetween⁻ f s e v∈ = Any-applyBetween⁻ f s e v∈
    -}


    ∉-filter₁ : ∀ {p} {P : A → Set p} (P? : Decidable P) {v} {xs} → v ∉ xs → v ∉ filter P? xs
    ∉-filter₁ P? {_} {[]}     _      ()
    ∉-filter₁ P? {v} {x ∷ xs} v∉x∷xs v∈f[x∷xs] with P? x | v∈f[x∷xs]
    ... | no  _ | v∈f[xs]       = ∉-filter₁ P? (v∉x∷xs ∘ there) v∈f[xs]
    ... | yes _ | here  v≈x     = v∉x∷xs (here v≈x)
    ... | yes _ | there v∈f[xs] = ∉-filter₁ P? (v∉x∷xs ∘ there) v∈f[xs]

    ∉-filter₂ : ∀ {p} {P : A → Set p} (P? : Decidable P) → P Respects _≈_ → ∀ {v} → ¬ P v → ∀ xs → v ∉ filter P? xs
    ∉-filter₂ P? resp ¬Pv [] ()
    ∉-filter₂ P? resp ¬Pv (x ∷ xs) v∈f[x∷xs] with P? x | v∈f[x∷xs]
    ... | no  _  | v∈f[xs]       = ∉-filter₂ P? resp ¬Pv xs v∈f[xs]
    ... | yes Px | here  v≈x     = ¬Pv (resp (sym v≈x) Px)
    ... | yes _  | there v∈f[xs] = ∉-filter₂ P? resp ¬Pv xs v∈f[xs]

    index-cong : ∀ {x y xs} → (x∈xs : x ∈ xs) (y∈xs : y ∈ xs) → Unique S xs → x ≈ y → index x∈xs ≡ index y∈xs
    index-cong (here x≈z)   (here y≈z)   _            x≈y = refl
    index-cong (here x≈z)   (there y∈xs) (z≉xs ∷ xs!) x≈y = contradiction (∈-resp-≈ S (trans (sym x≈y) x≈z) y∈xs) (All¬⇒¬Any z≉xs)
    index-cong (there x∈xs) (here y≈z)   (z≉xs ∷ xs!) x≈y = contradiction (∈-resp-≈ S (trans x≈y y≈z) x∈xs) (All¬⇒¬Any z≉xs)
    index-cong (there x∈xs) (there y∈xs) (_ ∷ xs!)    x≈y = cong Fin.suc (index-cong x∈xs y∈xs xs! x≈y)




  ------------------------------------
  -- Properties involving 2 setoids --
  ------------------------------------

  module _ {c₁ c₂ ℓ₁ ℓ₂} (S₁ : Setoid c₁ ℓ₁) (S₂ : Setoid c₂ ℓ₂) where

    open Setoid S₁ using () renaming (Carrier to A; _≈_ to _≈₁_; refl to refl₁; reflexive to reflexive₁; sym to sym₁; trans to trans₁)
    open Setoid S₂ using () renaming (Carrier to B; _≈_ to _≈₂_; refl to refl₂; reflexive to reflexive₂; sym to sym₂; trans to trans₂)
    open import Data.List.Membership.Setoid S₁ using () renaming (_∈_ to _∈₁_)
    open import Data.List.Membership.Setoid S₂ using () renaming (_∈_ to _∈₂_)

    {-
    ∈-mapMaybe : ∀ P {v xs a} → v ∈₁ xs → Eq _≈₂_ (P v) (just a) → (∀ {x y} → x ≈₁ y → Eq _≈₂_ (P x) (P y)) → a ∈₂ mapMaybe P xs
    ∈-mapMaybe _ {_} {[]}     ()
    ∈-mapMaybe P {v} {x ∷ xs} v∈xs Pᵥ≈justₐ P-resp-≈ with P x | inspect P x | v∈xs
    ... | nothing | [ Px≡nothing ] | here v≈x    = contradiction (Eq-trans trans₂ (Eq-trans trans₂ (Eq-reflexive reflexive₂ (≡-sym Px≡nothing)) (P-resp-≈ (sym₁ v≈x))) Pᵥ≈justₐ) λ()
    ... | nothing | [ _ ]          | there v∈xs₂ = ∈-mapMaybe P v∈xs₂ Pᵥ≈justₐ P-resp-≈
    ... | just b  | [ Px≡justb ]   | here v≈x    = here (drop-just (Eq-trans trans₂ (Eq-trans trans₂ (Eq-sym sym₂ Pᵥ≈justₐ) (P-resp-≈ v≈x)) (Eq-reflexive reflexive₂ Px≡justb)))
    ... | just b  | _              | there v∈xs₂ = there (∈-mapMaybe P v∈xs₂ Pᵥ≈justₐ P-resp-≈)
    -}


  ------------------------------------
  -- Properties involving 3 setoids --
  ------------------------------------

  module _ {c₁ c₂ c₃ ℓ₁ ℓ₂ ℓ₃} (S₁ : Setoid c₁ ℓ₁) (S₂ : Setoid c₂ ℓ₂) (S₃ : Setoid c₃ ℓ₃) where

    open Setoid S₁ using () renaming (Carrier to A; _≈_ to _≈₁_; refl to refl₁; sym to sym₁; trans to trans₁)
    open Setoid S₂ using () renaming (Carrier to B; _≈_ to _≈₂_; refl to refl₂; sym to sym₂; trans to trans₂)
    open Setoid S₃ using () renaming (Carrier to C; _≈_ to _≈₃_; refl to refl₃; sym to sym₃; trans to trans₃)
    open import Data.List.Membership.Setoid S₁ using () renaming (_∈_ to _∈₁_)
    open import Data.List.Membership.Setoid S₂ using () renaming (_∈_ to _∈₂_)
    open import Data.List.Membership.Setoid S₃ using () renaming (_∈_ to _∈₃_)

    open import Data.List.Membership.Setoid.Properties

    -- combine

    ∈-combine : ∀ {f} → f Preserves₂ _≈₁_ ⟶ _≈₂_ ⟶ _≈₃_ → ∀ {xs ys a b} → a ∈₁ xs → b ∈₂ ys → f a b ∈₃ combine f xs ys
    ∈-combine pres {_ ∷ _} {ys} (here  a≈x)  b∈ys = ∈-resp-≈ S₃ (pres (sym₁ a≈x) refl₂) (∈-++⁺ˡ S₃ (∈-map⁺ S₂ S₃ (pres refl₁) b∈ys))
    ∈-combine pres {_ ∷ _} {ys} (there a∈xs) b∈ys = ∈-++⁺ʳ S₃ (map _ ys) (∈-combine pres a∈xs b∈ys)

    combine-∈ : ∀ f xs ys {v} → v ∈₃ combine f xs ys → ∃₂ λ a b → a ∈₁ xs × b ∈₂ ys × v ≈₃ f a b
    combine-∈ f [] ys ()
    combine-∈ f (x ∷ xs) ys v∈map++com with ∈-++⁻ S₃ (map (f x) ys) v∈map++com
    combine-∈ f (x ∷ xs) ys v∈map++com | inj₁ v∈map with ∈-map⁻ S₂ S₃ v∈map
    ... | (b , b∈ys , v≈fxb) = x , b , here refl₁ , b∈ys , v≈fxb
    combine-∈ f (x ∷ xs) ys v∈map++com | inj₂ v∈com with combine-∈ f xs ys v∈com
    ... | (a , b , a∈xs , b∈ys , v≈fab) = a , b , there a∈xs , b∈ys , v≈fab

