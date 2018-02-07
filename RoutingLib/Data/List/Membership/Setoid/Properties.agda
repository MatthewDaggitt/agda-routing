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
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (nothing; just; Maybe; Eq; Eq-refl; Eq-sym; Eq-trans; drop-just)
open import Data.Empty using (⊥-elim)
open import Data.List hiding (any)
open import Data.List.Any using (here; there; any) renaming (map to mapₐ)
open import Data.List.Any.Properties
open import Data.Vec using (Vec; toList; fromList) renaming (_∈_ to _∈ᵥ_; here to hereᵥ; there to thereᵥ)
open import Data.Product using (∃; ∃₂; _×_; _,_; swap) renaming (map to mapₚ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (true; false; if_then_else_)
open import Relation.Unary using (Decidable; _⇒_) renaming (_⊆_ to _⋐_)
open import Algebra.FunctionProperties using (Op₂; RightIdentity; Selective)

open import RoutingLib.Data.List
open import RoutingLib.Data.Maybe using (Eq-reflexive)
open import RoutingLib.Data.Maybe.Properties using (just-injective)
import RoutingLib.Data.List.Membership.Setoid as Membership
open import RoutingLib.Data.List.Any.Properties
open import RoutingLib.Data.List.Permutation using (_⇿_; _◂_≡_; _∷_; []; here; there)
open import RoutingLib.Data.List.Uniqueness.Setoid using (Unique; _∷_)
open import RoutingLib.Data.List.All using ([]; _∷_)


module RoutingLib.Data.List.Membership.Setoid.Properties where

  -----------------------------------
  -- Properties involving 1 setoid --
  -----------------------------------

  module _ {c ℓ} (S : Setoid c ℓ) where

    open Setoid S renaming (Carrier to A; refl to ≈-refl)
    open Setoid (list-setoid S) using () renaming (_≈_ to _≈ₗ_; sym to symₗ; refl to reflₗ)

    open import Data.List.Any.Membership S using (_∈_; _∉_; _⊆_)
    open import Data.List.Any.Membership (list-setoid S) using () renaming (_∈_ to _∈ₗ_)

    ∈-dec : Decidable₂ _≈_ → Decidable₂ _∈_
    ∈-dec _≟_ x [] = no λ()
    ∈-dec _≟_ x (y ∷ ys) with x ≟ y | ∈-dec _≟_ x ys
    ... | yes x≈y | _        = yes (here x≈y)
    ... | _       | yes x∈ys = yes (there x∈ys)
    ... | no  x≉y | no  x∉ys = no (λ {(here x≈y) → x≉y x≈y; (there x∈ys) → x∉ys x∈ys})

    ∈-resp-≈ : ∀ {v w xs} → v ∈ xs → v ≈ w → w ∈ xs
    ∈-resp-≈ (here v≈x)   v≈w = here (trans (sym v≈w) v≈x)
    ∈-resp-≈ (there v∈xs) v≈w = there (∈-resp-≈ v∈xs v≈w)

    ∉-resp-≈ : ∀ {v w xs} → v ∉ xs → v ≈ w → w ∉ xs
    ∉-resp-≈ v∉xs v≈w w∈xs = v∉xs (∈-resp-≈ w∈xs (sym v≈w))

    ∈-resp-≈ₗ : ∀ {v xs ys} → v ∈ xs → xs ≈ₗ ys → v ∈ ys
    ∈-resp-≈ₗ (here v≈x) (x≈y ∷ _) = here (trans v≈x x≈y)
    ∈-resp-≈ₗ (there v∈xs) (_ ∷ xs≈ys) = there (∈-resp-≈ₗ v∈xs xs≈ys)

    ∉-resp-≈ₗ : ∀ {v xs ys} → v ∉ xs → xs ≈ₗ ys → v ∉ ys
    ∉-resp-≈ₗ v∉xs xs≈ys v∈ys = v∉xs (∈-resp-≈ₗ v∈ys (symₗ xs≈ys))

    -- ++ operation

    -- stdlib
    ∈-++⁺ʳ : ∀ {v} xs {ys} → v ∈ ys → v ∈ xs ++ ys
    ∈-++⁺ʳ = ++⁺ʳ

    -- stdlib
    ∈-++⁺ˡ : ∀ {v xs ys} → v ∈ xs → v ∈ xs ++ ys
    ∈-++⁺ˡ = ++⁺ˡ

    -- stdlib
    ∈-++⁻ : ∀ {v} xs {ys} → v ∈ xs ++ ys → v ∈ xs ⊎ v ∈ ys
    ∈-++⁻ = ++⁻

    -- concat

    ∈-concat⁺ : ∀ {v xs xss} → v ∈ xs → xs ∈ₗ xss → v ∈ concat xss
    ∈-concat⁺ {_} {_ ∷ _} {[] ∷ _}         (here _)     (here ())
    ∈-concat⁺ {_} {_ ∷ _} {[] ∷ _}         (there _)    (here ())
    ∈-concat⁺ {_} {_ ∷ _} {(_ ∷ _) ∷ _}    (here v≈x)   (here (x≈y ∷ _))   = here (trans v≈x x≈y)
    ∈-concat⁺ {_} {_ ∷ _} {(y ∷ ys) ∷ xss} (there v∈xs) (here (_ ∷ xs≈ys)) = there (∈-concat⁺ {xss = ys ∷ xss} v∈xs (here xs≈ys))
    ∈-concat⁺ {_} {_ ∷ _} {ys ∷ xss}       v∈xs         (there s)          = ∈-++⁺ʳ ys (∈-concat⁺ v∈xs (s))

    ∈-concat⁻ : ∀ {v xss} → v ∈ concat xss → ∃ λ ys → v ∈ ys × ys ∈ₗ xss
    ∈-concat⁻ {_} {[]} ()
    ∈-concat⁻ {_} {[] ∷ []} ()
    ∈-concat⁻ {_} {[] ∷ (xs ∷ xss)} v∈concat[xs∷xss] with ∈-concat⁻ v∈concat[xs∷xss]
    ... | (ys , v∈ys , ys∈xss) = ys , v∈ys , there ys∈xss
    ∈-concat⁻ {_} {(x ∷ xs) ∷ xss} (here v≈x) = x ∷ xs , here v≈x , here reflₗ
    ∈-concat⁻ {_} {(x ∷ xs) ∷ xss} (there v∈concat[xs∷xss]) with ∈-concat⁻ {xss = xs ∷ xss} v∈concat[xs∷xss]
    ... | (ys , v∈ys , here ys≈xs)   = x ∷ xs , ∈-resp-≈ₗ (there v∈ys) (≈-refl ∷ ys≈xs) , here reflₗ
    ... | (ys , v∈ys , there ys∈xss) = ys , v∈ys , there ys∈xss


    -- tabulate

    ∈-tabulate⁺ : ∀ {n} (f : Fin n → A) i → f i ∈ tabulate f
    ∈-tabulate⁺ f i = tabulate⁺ i ≈-refl
    
    ∈-tabulate⁻ : ∀ {n} {f : Fin n → A} {x} → x ∈ tabulate f → ∃ λ i → x ≈ f i
    ∈-tabulate⁻ = tabulate⁻
    

    -- applyUpTo

    ∈-applyUpTo⁺ : ∀ f {n i} → i < n → f i ∈ applyUpTo f n
    ∈-applyUpTo⁺ f (s≤s z≤n)       = here ≈-refl
    ∈-applyUpTo⁺ f (s≤s (s≤s i≤n)) = there (∈-applyUpTo⁺ (f ∘ suc) (s≤s i≤n))

    ∈-applyBetween⁺ : ∀ f {s e i} → s ≤ i → i < e → f i ∈ applyBetween f s e
    ∈-applyBetween⁺ f s≤i i<e = Any-applyBetween⁺ f s≤i i<e ≈-refl
    
    ∈-applyBetween⁻ : ∀ f s e {v} → v ∈ applyBetween f s e → ∃ λ i → s ≤ i × i < e × v ≈ f i
    ∈-applyBetween⁻ f s e v∈ = Any-applyBetween⁻ f s e v∈
    

    -- dfilter

    ∈-dfilter⁺ : ∀ {p} {P : A → Set p} (P? : Decidable P) → P Respects _≈_ →
                 ∀ {v} → P v → ∀ {xs} → v ∈ xs → v ∈ dfilter P? xs
    ∈-dfilter⁺ P? resp Pv {x ∷ _} (here v≈x)   with P? x
    ... | yes _   = here v≈x
    ... | no  ¬Px = contradiction (resp v≈x Pv) ¬Px
    ∈-dfilter⁺ P? resp Pv {x ∷ _} (there v∈xs) with P? x
    ... | yes _ = there (∈-dfilter⁺ P? resp Pv v∈xs)
    ... | no  _ = ∈-dfilter⁺ P? resp Pv v∈xs

    ∈-dfilter⁻ : ∀ {p} {P : A → Set p} (P? : Decidable P) → P Respects _≈_ →
                 ∀ {v xs} → v ∈ dfilter P? xs → v ∈ xs × P v
    ∈-dfilter⁻ P? resp {v} {[]}     ()
    ∈-dfilter⁻ P? resp {v} {x ∷ xs} v∈dfilter with P? x | v∈dfilter
    ... | no  _  | v∈df       = mapₚ there id (∈-dfilter⁻ P? resp v∈df)
    ... | yes Px | here  v≈x  = here v≈x , resp (sym v≈x) Px
    ... | yes Px | there v∈df = mapₚ there id (∈-dfilter⁻ P? resp v∈df)

    ∉-dfilter₁ : ∀ {p} {P : A → Set p} (P? : Decidable P) {v} {xs} → v ∉ xs → v ∉ dfilter P? xs
    ∉-dfilter₁ P? {_} {[]}     _      ()
    ∉-dfilter₁ P? {v} {x ∷ xs} v∉x∷xs v∈f[x∷xs] with P? x | v∈f[x∷xs]
    ... | no  _ | v∈f[xs]       = ∉-dfilter₁ P? (v∉x∷xs ∘ there) v∈f[xs]
    ... | yes _ | here  v≈x     = v∉x∷xs (here v≈x)
    ... | yes _ | there v∈f[xs] = ∉-dfilter₁ P? (v∉x∷xs ∘ there) v∈f[xs]

    ∉-dfilter₂ : ∀ {p} {P : A → Set p} (P? : Decidable P) → P Respects _≈_ → ∀ {v} → ¬ P v → ∀ xs → v ∉ dfilter P? xs
    ∉-dfilter₂ P? resp ¬Pv [] ()
    ∉-dfilter₂ P? resp ¬Pv (x ∷ xs) v∈f[x∷xs] with P? x | v∈f[x∷xs]
    ... | no  _  | v∈f[xs]       = ∉-dfilter₂ P? resp ¬Pv xs v∈f[xs]
    ... | yes Px | here  v≈x     = ¬Pv (resp (sym v≈x) Px)
    ... | yes _  | there v∈f[xs] = ∉-dfilter₂ P? resp ¬Pv xs v∈f[xs]

    
    ⊆-dfilter : ∀ {p} {P : A → Set p} (P? : Decidable P)
                  {q} {Q : A → Set q} (Q? : Decidable Q) → 
                  P ⋐ Q → 
                  ∀ xs → dfilter P? xs ⊆ dfilter Q? xs
    ⊆-dfilter P? Q? P⋐Q [] ()
    ⊆-dfilter P? Q? P⋐Q (x ∷ xs) v∈f[x∷xs] with P? x | Q? x
    ... | no  _  | no  _  = ⊆-dfilter P? Q? P⋐Q xs v∈f[x∷xs]
    ... | yes Px | no ¬Qx = contradiction (P⋐Q Px) ¬Qx
    ... | no  _  | yes _  = there (⊆-dfilter P? Q? P⋐Q xs v∈f[x∷xs])
    ... | yes _  | yes _  with v∈f[x∷xs]
    ...   | here  v≈x     = here v≈x
    ...   | there v∈f[xs] = there (⊆-dfilter P? Q? P⋐Q xs v∈f[xs])

    foldr-∈ : ∀ {_•_} → Selective _≈_ _•_ → ∀ e xs → foldr _•_ e xs ≈ e ⊎ foldr _•_ e xs ∈ xs 
    foldr-∈ {_}   •-sel i [] = inj₁ ≈-refl
    foldr-∈ {_•_} •-sel i (x ∷ xs) with •-sel x (foldr _•_ i xs)
    ... | inj₁ x•f≈x = inj₂ (here x•f≈x)
    ... | inj₂ x•f≈f with foldr-∈ •-sel i xs
    ...   | inj₁ f≈i  = inj₁ (trans x•f≈f f≈i)
    ...   | inj₂ f∈xs = inj₂ (∈-resp-≈ (there f∈xs) (sym x•f≈f))

    ∈-perm : ∀ {x xs ys} → x ∈ xs → xs ⇿ ys → x ∈ ys
    ∈-perm = Any-⇿

    ∈-length : ∀ {x xs} → x ∈ xs → 1 ≤ length xs
    ∈-length {_} {_ ∷ xs} (here px)    = s≤s z≤n
    ∈-length {_} {_ ∷ xs} (there x∈xs) = ≤-trans (∈-length x∈xs) (n≤1+n (length xs))
    
    ∈-lookup : ∀ xs i → lookup xs i ∈ xs
    ∈-lookup []       ()
    ∈-lookup (x ∷ xs) fzero    = here ≈-refl
    ∈-lookup (x ∷ xs) (fsuc i) = there (∈-lookup xs i)

    index-cong : ∀ {x y xs} → (x∈xs : x ∈ xs) (y∈xs : y ∈ xs) → Unique S xs → x ≈ y → index x∈xs ≡ index y∈xs
    index-cong (here x≈z)   (here y≈z)   _            x≈y = refl
    index-cong (here x≈z)   (there y∈xs) (z≉xs ∷ xs!) x≈y = contradiction (∈-resp-≈ y∈xs (trans (sym x≈y) x≈z)) (All¬⇒¬Any z≉xs)
    index-cong (there x∈xs) (here y≈z)   (z≉xs ∷ xs!) x≈y = contradiction (∈-resp-≈ x∈xs (trans x≈y y≈z)) (All¬⇒¬Any z≉xs)
    index-cong (there x∈xs) (there y∈xs) (_ ∷ xs!)    x≈y = cong fsuc (index-cong x∈xs y∈xs xs! x≈y)
    

    
    
  ------------------------------------
  -- Properties involving 2 setoids --
  ------------------------------------

  module _ {c₁ c₂ ℓ₁ ℓ₂} (S₁ : Setoid c₁ ℓ₁) (S₂ : Setoid c₂ ℓ₂) where

    open Setoid S₁ using () renaming (Carrier to A; _≈_ to _≈₁_; refl to refl₁; reflexive to reflexive₁; sym to sym₁; trans to trans₁)
    open Setoid S₂ using () renaming (Carrier to B; _≈_ to _≈₂_; refl to refl₂; reflexive to reflexive₂; sym to sym₂; trans to trans₂)
    open import Data.List.Any.Membership S₁ using () renaming (_∈_ to _∈₁_)
    open import Data.List.Any.Membership S₂ using () renaming (_∈_ to _∈₂_)

    ∈-map⁺ : ∀ {f} → f Preserves _≈₁_ ⟶ _≈₂_ → ∀ {v xs} → v ∈₁ xs → f v ∈₂ map f xs
    ∈-map⁺ f-pres v∈xs = map⁺ (mapₐ f-pres v∈xs)

    ∈-map⁻ : ∀ {f v xs} → v ∈₂ map f xs → ∃ λ a → a ∈₁ xs × v ≈₂ f a
    ∈-map⁻ {xs = []}     ()
    ∈-map⁻ {xs = x ∷ xs} (here v≈fx) = x , here refl₁ , v≈fx
    ∈-map⁻ {xs = x ∷ xs} (there v∈mapfxs) with ∈-map⁻ v∈mapfxs
    ... | a , a∈xs , v≈fa = a , there a∈xs , v≈fa

    ∈-gfilter : ∀ P {v xs a} → v ∈₁ xs → Eq _≈₂_ (P v) (just a) → (∀ {x y} → x ≈₁ y → Eq _≈₂_ (P x) (P y)) → a ∈₂ gfilter P xs
    ∈-gfilter _ {_} {[]}     ()
    ∈-gfilter P {v} {x ∷ xs} v∈xs Pᵥ≈justₐ P-resp-≈ with P x | inspect P x | v∈xs
    ... | nothing | [ Px≡nothing ] | here v≈x    = contradiction (Eq-trans trans₂ (Eq-trans trans₂ (Eq-reflexive reflexive₂ (≡-sym Px≡nothing)) (P-resp-≈ (sym₁ v≈x))) Pᵥ≈justₐ) λ()
    ... | nothing | [ _ ]          | there v∈xs₂ = ∈-gfilter P v∈xs₂ Pᵥ≈justₐ P-resp-≈
    ... | just b  | [ Px≡justb ]   | here v≈x    = here (drop-just (Eq-trans trans₂ (Eq-trans trans₂ (Eq-sym sym₂ Pᵥ≈justₐ) (P-resp-≈ v≈x)) (Eq-reflexive reflexive₂ Px≡justb)))
    ... | just b  | _              | there v∈xs₂ = there (∈-gfilter P v∈xs₂ Pᵥ≈justₐ P-resp-≈)



  ------------------------------------
  -- Properties involving 3 setoids --
  ------------------------------------

  module _ {c₁ c₂ c₃ ℓ₁ ℓ₂ ℓ₃} (S₁ : Setoid c₁ ℓ₁) (S₂ : Setoid c₂ ℓ₂) (S₃ : Setoid c₃ ℓ₃) where

    open Setoid S₁ using () renaming (Carrier to A; _≈_ to _≈₁_; refl to refl₁; sym to sym₁; trans to trans₁)
    open Setoid S₂ using () renaming (Carrier to B; _≈_ to _≈₂_; refl to refl₂; sym to sym₂; trans to trans₂)
    open Setoid S₃ using () renaming (Carrier to C; _≈_ to _≈₃_; refl to refl₃; sym to sym₃; trans to trans₃)
    open import Data.List.Any.Membership S₁ using () renaming (_∈_ to _∈₁_)
    open import Data.List.Any.Membership S₂ using () renaming (_∈_ to _∈₂_)
    open import Data.List.Any.Membership S₃ using () renaming (_∈_ to _∈₃_)

    -- combine

    ∈-combine : ∀ {f} → f Preserves₂ _≈₁_ ⟶ _≈₂_ ⟶ _≈₃_ → ∀ {xs ys a b} → a ∈₁ xs → b ∈₂ ys → f a b ∈₃ combine f xs ys
    ∈-combine pres {_ ∷ _} {ys} (here  a≈x)  b∈ys = ∈-resp-≈ S₃ (∈-++⁺ˡ S₃ (∈-map⁺ S₂ S₃ (pres refl₁) b∈ys)) (pres (sym₁ a≈x) refl₂)
    ∈-combine pres {_ ∷ _} {ys} (there a∈xs) b∈ys = ∈-++⁺ʳ S₃ (map _ ys) (∈-combine pres a∈xs b∈ys)

    combine-∈ : ∀ f xs ys {v} → v ∈₃ combine f xs ys → ∃₂ λ a b → a ∈₁ xs × b ∈₂ ys × v ≈₃ f a b
    combine-∈ f [] ys ()
    combine-∈ f (x ∷ xs) ys v∈map++com with ∈-++⁻ S₃ (map (f x) ys) v∈map++com
    combine-∈ f (x ∷ xs) ys v∈map++com | inj₁ v∈map with ∈-map⁻ S₂ S₃ v∈map
    ... | (b , b∈ys , v≈fxb) = x , b , here refl₁ , b∈ys , v≈fxb
    combine-∈ f (x ∷ xs) ys v∈map++com | inj₂ v∈com with combine-∈ f xs ys v∈com
    ... | (a , b , a∈xs , b∈ys , v≈fab) = a , b , there a∈xs , b∈ys , v≈fab



  
