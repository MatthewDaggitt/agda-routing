open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_; cong; subst; subst₂; inspect; [_]) renaming (trans to ≡-trans; sym to ≡-sym; setoid to ≡-setoid)
open import Relation.Binary.List.Pointwise using ([]; _∷_) renaming (setoid to list-setoid)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary using (¬_)
open import Function using (_∘_)
open import Data.List.Any as Any using (here; there)
open import Data.List.All using (All; _∷_; [])
open import Data.Nat using (_≤_; suc; s≤s; z≤n)
open import Data.Maybe using (nothing; just; Maybe; Eq; drop-just)
open import Data.Empty using (⊥-elim)
open import Algebra.FunctionProperties using (Op₂; RightIdentity)
open import Data.List
open import Data.Vec using (Vec; toList; fromList) renaming (_∈_ to _∈ᵥ_; here to hereᵥ; there to thereᵥ)
open import Data.Product using (∃; _×_; _,_; swap)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (true; false; if_then_else_)
open import Relation.Unary using () renaming (_⊆_ to _⋐_)

open import RoutingLib.Algebra.FunctionProperties using (Selective)
open import RoutingLib.Data.List.Any.Properties
open import RoutingLib.Data.Maybe.Base using (predBoolToMaybe)
open import RoutingLib.Data.Maybe.Properties using (just-injective) renaming (reflexive to eq-reflexive; sym to eq-sym; trans to eq-trans)

module RoutingLib.Data.List.Any.GenericMembership {c ℓ} (setoid : Setoid c ℓ) where

  open Setoid setoid renaming (Carrier to A; refl to ≈-refl)
  open Setoid (list-setoid setoid) using () renaming (_≈_ to _≈ₗ_; sym to symₗ; refl to reflₗ) 

  open Any.Membership setoid using (_∈_; _∉_; _⊆_)
  open Any.Membership (list-setoid setoid) using () renaming (_∈_ to _∈ₗ_)



  module Double {c₂ ℓ₂} (setoid₂ : Setoid c₂ ℓ₂) where
    
    open Setoid setoid₂ using () renaming (Carrier to B; _≈_ to _≈₂_; refl to refl₂; sym to sym₂; trans to trans₂)
    open Any.Membership setoid₂  using () renaming (_∈_ to _∈₂_)

    ∈-map : ∀ {v xs f} → f Preserves _≈_ ⟶ _≈₂_ → v ∈ xs → f v ∈₂ map f xs
    ∈-map {_} {x ∷ xs} pe (here v≈x)   = here (pe v≈x)
    ∈-map {_} {x ∷ xs} pe (there v∈xs) = there (∈-map pe v∈xs)

    map-∃-∈ : ∀ {v xs f} → v ∈₂ map f xs → ∃ λ y → y ∈ xs × v ≈₂ f y
    map-∃-∈ {xs = []} ()
    map-∃-∈ {xs = x ∷ xs} (here v≈fx) = x , here ≈-refl , v≈fx
    map-∃-∈ {xs = x ∷ xs} (there v∈mapfxs) with map-∃-∈ v∈mapfxs
    ... | y , y∈xs , v≈fy = y , there y∈xs , v≈fy

    ∈-gfilter : ∀ P {v xs a} → v ∈ xs → Eq _≈₂_ (P v) (just a) → (∀ {x y} → x ≈ y → Eq _≈₂_ (P x) (P y)) → a ∈₂ gfilter P xs
    ∈-gfilter _ {_} {[]}     ()
    ∈-gfilter P {v} {x ∷ xs} v∈xs Pᵥ≈justₐ P-resp-≈ with P x | inspect P x | v∈xs
    ... | nothing | [ Px≡nothing ] | here v≈x    = contradiction (eq-trans trans₂ (eq-trans trans₂ (eq-reflexive refl₂ (≡-sym Px≡nothing)) (P-resp-≈ (sym v≈x))) Pᵥ≈justₐ) λ()
    ... | nothing | [ _ ]          | there v∈xs₂ = ∈-gfilter P v∈xs₂ Pᵥ≈justₐ P-resp-≈
    ... | just b  | [ Px≡justb ]   | here v≈x    = here (drop-just (eq-trans trans₂ (eq-trans trans₂ (eq-sym sym₂ Pᵥ≈justₐ) (P-resp-≈ v≈x)) (eq-reflexive refl₂ Px≡justb)))
    ... | just b  | _              | there v∈xs₂ = there (∈-gfilter P v∈xs₂ Pᵥ≈justₐ P-resp-≈)

  open Double public


  ----------------------
  -- Pushed to stdlib --
  ----------------------

  ++-∈ₗ : ∀ {v ys} xs → v ∈ ys → v ∈ xs ++ ys
  ++-∈ₗ {_} {[]}     _        ()
  ++-∈ₗ {_} {y ∷ ys} []       v∈y∷ys   = v∈y∷ys
  ++-∈ₗ {_} {y ∷ ys} (x ∷ xs) v∈y∷ys   = there (++-∈ₗ xs v∈y∷ys)

  ++-∈ᵣ : ∀ {v ys} xs → v ∈ xs → v ∈ xs ++ ys
  ++-∈ᵣ []       ()
  ++-∈ᵣ (x ∷ xs) (here v≈x)   = here v≈x
  ++-∈ᵣ (x ∷ xs) (there v∈xs) = there (++-∈ᵣ _ v∈xs)

  concat-∈ : ∀ {v xs xss} → v ∈ xs → xs ∈ₗ xss → v ∈ concat xss
  concat-∈ {_} {_ ∷ _} {[] ∷ _}         (here _)     (here ())
  concat-∈ {_} {_ ∷ _} {[] ∷ _}         (there _)    (here ())
  concat-∈ {_} {_ ∷ _} {(_ ∷ _) ∷ _}    (here v≈x)   (here (x≈y ∷ _))   = here (trans v≈x x≈y)
  concat-∈ {_} {_ ∷ _} {(y ∷ ys) ∷ xss} (there v∈xs) (here (_ ∷ xs≈ys)) = there (concat-∈ {xss = ys ∷ xss} v∈xs (here xs≈ys))
  concat-∈ {_} {_ ∷ _} {ys ∷ xss}       v∈xs         (there s)          = ++-∈ₗ ys (concat-∈ v∈xs (s))


  -----------------------
  -- To push to stdlib --
  -----------------------

  
  filter-pres-∉ : ∀ P {v xs} → v ∉ xs → v ∉ filter P xs
  filter-pres-∉ P {v} {[]} _ ()
  filter-pres-∉ P {v} {x ∷ xs} v∉x∷xs with predBoolToMaybe P x | inspect (predBoolToMaybe P) x
  ... | nothing | _ = filter-pres-∉ P (v∉x∷xs ∘ there)
  ... | just y  | [ t ] with P x
  ...   | true  = λ {(here v≈y) → (v∉x∷xs ∘ here) (trans v≈y (sym (reflexive (just-injective t)))); (there v∈fxs) → (filter-pres-∉ P (v∉x∷xs ∘ there)) v∈fxs}
  ...   | false = contradiction t λ()


  -----------
  -- Other --
  -----------


  gfilter-∈ : ∀ P {v} xs → v ∈ gfilter P xs → ∃ λ w → w ∈ xs × Eq _≈_ (P w) (just v) 
  gfilter-∈ P [] ()
  gfilter-∈ P (x ∷ xs) _ with P x | inspect P x
  gfilter-∈ P (x ∷ xs) v∈fₚxs         | nothing | _ with gfilter-∈ P xs v∈fₚxs
  ... | (w , w∈xs , Pw≈justᵥ) = w , there w∈xs , Pw≈justᵥ
  gfilter-∈ P (x ∷ xs) (here v≈w)     | just w  | [ Px≡justw ] = x , (here ≈-refl) , eq-trans trans (eq-reflexive ≈-refl Px≡justw) (just (sym v≈w))
  gfilter-∈ P (x ∷ xs) (there v∈fₚxs) | just _  | _ with gfilter-∈ P xs v∈fₚxs
  ... | (w , w∈xs , Pw≈justᵥ) = w , there w∈xs , Pw≈justᵥ



  ∈-resp-≈ : ∀ {v w xs} → v ∈ xs → v ≈ w → w ∈ xs
  ∈-resp-≈ (here v≈x) v≈w = here (trans (sym v≈w) v≈x)
  ∈-resp-≈ (there v∈xs) v≈w = there (∈-resp-≈ v∈xs v≈w)

  ∉-resp-≈ : ∀ {v w xs} → v ∉ xs → v ≈ w → w ∉ xs
  ∉-resp-≈ v∉xs v≈w w∈xs = v∉xs (∈-resp-≈ w∈xs (sym v≈w))

  ∈-resp-≈ₗ : ∀ {v xs ys} → v ∈ xs → xs ≈ₗ ys → v ∈ ys
  ∈-resp-≈ₗ (here v≈x) (x≈y ∷ _) = here (trans v≈x x≈y)
  ∈-resp-≈ₗ (there v∈xs) (_ ∷ xs≈ys) = there (∈-resp-≈ₗ v∈xs xs≈ys) 

  ∉-resp-≈ₗ : ∀ {v xs ys} → v ∉ xs → xs ≈ₗ ys → v ∉ ys
  ∉-resp-≈ₗ v∉xs xs≈ys v∈ys = v∉xs (∈-resp-≈ₗ v∈ys (symₗ xs≈ys))



  -- Types 

  -- Disjoint sets
  Disjoint : Rel (List A) (ℓ ⊔ c)
  Disjoint xs ys = ∀ {v} → ¬ (v ∈ xs × v ∈ ys)

  disjoint-sym : Symmetric Disjoint
  disjoint-sym xs∩ys=∅ ∈both = xs∩ys=∅ (swap ∈both)

  disjoint-contract₁ : ∀ {x xs ys} → Disjoint (x ∷ xs) ys → Disjoint xs ys
  disjoint-contract₁ x∷xs∩ys=∅ (v∈xs , v∈ys) = x∷xs∩ys=∅ (there v∈xs , v∈ys)

  disjoint-contract₂ : ∀ {xs y ys} → Disjoint xs (y ∷ ys) → Disjoint xs ys
  disjoint-contract₂ xs∩y∷ys=∅ (v∈xs , v∈ys) = xs∩y∷ys=∅ (v∈xs , there v∈ys)

  disjoint-contract₃ : ∀ {x xs ys} → Disjoint (x ∷ xs) ys → Disjoint (x ∷ []) ys
  disjoint-contract₃ x∷xs∩ys=∅ (here v≈x , v∈ys) = x∷xs∩ys=∅ ((here v≈x) , v∈ys)
  disjoint-contract₃ x∷xs∩ys=∅ (there () , v∈ys)

  disjoint-[] : ∀ xs → Disjoint xs []
  disjoint-[] _ (_ , ())

  ∈xs⇨∉ys : ∀ {xs ys} → Disjoint xs ys → ∀ {v} → v ∈ xs → v ∉ ys
  ∈xs⇨∉ys xs∩ys=∅ v∈xs v∈ys = xs∩ys=∅ (v∈xs , v∈ys)

  disjoint-concat : ∀ {vs xss} → All (Disjoint vs) xss → Disjoint vs (concat xss)
  disjoint-concat [] (_ , ())
  disjoint-concat {xss = xs ∷ xss} (vs∩xs=∅ ∷ vs∩xss=∅) (v∈vs , v∈xs++concatxss) with ++⁻ xs v∈xs++concatxss
  ... | inj₁ v∈xs  = vs∩xs=∅ (v∈vs , v∈xs)
  ... | inj₂ v∈xss = disjoint-concat vs∩xss=∅ (v∈vs , v∈xss) 



  -- Converting a vector to a list does not change the elements within
  toList-preserves-∈ : ∀ {n v} {xs : Vec A n} → v ∈ᵥ xs → v ∈ toList xs
  toList-preserves-∈ hereᵥ = here (reflexive refl)
  toList-preserves-∈ (thereᵥ v∈xs) = there (toList-preserves-∈ v∈xs)
  
  concat-∃-∈ : ∀ {v xss} → v ∈ concat xss → ∃ λ ys → (v ∈ ys × ys ∈ₗ xss) 
  concat-∃-∈ {_} {[]} ()
  concat-∃-∈ {_} {[] ∷ []} ()
  concat-∃-∈ {_} {[] ∷ (xs ∷ xss)} v∈concat[xs∷xss] with concat-∃-∈ v∈concat[xs∷xss]
  ... | (ys , v∈ys , ys∈xss) = ys , v∈ys , there ys∈xss
  concat-∃-∈ {_} {(x ∷ xs) ∷ xss} (here v≈x) = x ∷ xs , here v≈x , here reflₗ
  concat-∃-∈ {_} {(x ∷ xs) ∷ xss} (there v∈concat[xs∷xss]) with concat-∃-∈ {xss = xs ∷ xss} v∈concat[xs∷xss]
  ... | (ys , v∈ys , here ys≈xs) = x ∷ xs , ∈-resp-≈ₗ (there v∈ys) (≈-refl ∷ ys≈xs) , here reflₗ
  ... | (ys , v∈ys , there ys∈xss) = ys , v∈ys , there ys∈xss

  ∈-contract : ∀ {v x xs} → v ∈ x ∷ xs → ¬ (v ≈ x) → v ∈ xs
  ∈-contract (here v≈x)   v≉x = contradiction v≈x v≉x
  ∈-contract (there v∈xs) _   = v∈xs

  ⊆-contractᵣ : ∀ {y xs ys} → xs ⊆ y ∷ ys → y ∉ xs → xs ⊆ ys
  ⊆-contractᵣ xs⊆y∷ys y∉xs v∈xs with xs⊆y∷ys v∈xs
  ... | here  v≈y  = contradiction (∈-resp-≈ v∈xs v≈y) y∉xs
  ... | there v∈ys = v∈ys 



  selective-foldr : ∀ {_•_ i x xs} → All (λ v → v • i ≈ v) (x ∷ xs) → Selective _≈_ _•_ → foldr _•_ i (x ∷ xs) ∈ x ∷ xs
  selective-foldr           {x = x} {[]}     (x•i≈x ∷ _) _     = here x•i≈x
  selective-foldr {_•_} {i} {x = x} {y ∷ xs} (x•i≈x ∷ r) •-sel with •-sel x (foldr _•_ i (y ∷ xs))
  ... | inj₁ x•f≈x = here x•f≈x
  ... | inj₂ x•f≈f with selective-foldr r •-sel
  ...   | f∈y∷xs = there (∈-resp-≈ f∈y∷xs (sym x•f≈f))


  selective-foldr' : ∀ {_•_} → Selective _≈_ _•_ → ∀ i xs → foldr _•_ i xs ∈ i ∷ xs
  selective-foldr' {_}   sel i [] = here ≈-refl
  selective-foldr' {_•_} sel i (x ∷ xs) with sel x (foldr _•_ i xs)
  ... | inj₁ x•f≈x = there (here x•f≈x)
  ... | inj₂ x•f≈f with selective-foldr' sel i xs
  ...   | here  f≈i  = here (trans x•f≈f f≈i)
  ...   | there f∈xs = there (∈-resp-≈ (there f∈xs) (sym x•f≈f))



  -- Removal

  remove : ∀ {v xs} → v ∈ xs → List A
  remove {xs = x ∷ xs} (here v≈x) = xs
  remove {xs = x ∷ xs} (there v∈xs) = x ∷ (remove v∈xs)

  remove-∈ : ∀ {v w xs} → (v∈xs : v ∈ xs) → w ∈ xs → ¬ (w ≈ v) → w ∈ remove v∈xs
  remove-∈ (here v≈x)   (here w≈x)   w≉v = contradiction (trans w≈x (sym v≈x)) w≉v
  remove-∈ (there v∈xs) (here w≈x)   _   = here w≈x
  remove-∈ (here v≈x)   (there w∈xs) _   = w∈xs
  remove-∈ (there v∈xs) (there w∈xs) w≉v   = there (remove-∈ v∈xs w∈xs w≉v)

  ∈-remove : ∀ {v w ys} → (w∈ys : w ∈ ys) → v ∈ ys → ¬ (w ≈ v) → v ∈ remove w∈ys
  ∈-remove {_} {_} {y ∷ ys} (here  w≈y)  (here  v≈y)  w≉v = contradiction (trans w≈y (sym v≈y)) w≉v
  ∈-remove {_} {_} {y ∷ ys} (here  w≈y)  (there v∈ys) w≉v = v∈ys
  ∈-remove {_} {_} {y ∷ ys} (there w∈ys) (here  v≈y)  w≉v = here v≈y
  ∈-remove {_} {_} {y ∷ ys} (there w∈ys) (there v∈ys) w≉v = there (∈-remove w∈ys v∈ys w≉v)

  ⊆-remove : ∀ {v xs ys} → xs ⊆ ys → (v∈ys : v ∈ ys) → v ∉ xs → xs ⊆ remove v∈ys
  ⊆-remove xs⊆ys (here v≈y)   v∉xs w∈xs with xs⊆ys w∈xs
  ... | here  w≈y  = contradiction (∈-resp-≈ w∈xs (trans w≈y (sym v≈y))) v∉xs
  ... | there w∈ys = w∈ys
  ⊆-remove xs⊆ys (there v∈ys) v∉xs w∈xs with xs⊆ys w∈xs
  ... | here  w≈y  = here w≈y
  ... | there w∈ys = there (remove-∈ v∈ys w∈ys (v∉xs ∘ (∈-resp-≈ w∈xs)))

  length-remove : ∀ {v xs} → (v∈xs : v ∈ xs) → suc (length (remove v∈xs)) ≡ length xs
  length-remove (here v≈x)   = refl
  length-remove (there v∈xs) = cong suc (length-remove v∈xs)


  ∈-filter : ∀ {P} → (∀ {x y} → x ≈ y → P x ≡ P y) → ∀ {v xs} → v ∈ xs → P v ≡ true → v ∈ filter P xs
  ∈-filter {P} P-resp-≈ {v} {xs} v∈xs Pv = ∈-gfilter setoid (λ v → if (P v) then just v else nothing) v∈xs test resp
    where

    test : Eq _≈_ (if P v then just v else nothing) (just v)
    test rewrite Pv = just ≈-refl

    resp : ∀ {x y} → x ≈ y → Eq _≈_ (if P x then just x else nothing) (if P y then just y else nothing)
    resp {x} {y} x≈y rewrite (P-resp-≈ x≈y) with P y
    ... | false = nothing
    ... | true  = just x≈y
  
  ∉-filter : ∀ {P} → (∀ {x y} → x ≈ y → P x ≡ P y) → ∀ {v} → P v ≡ false → ∀ xs → v ∉ filter P xs
  ∉-filter {_} P-resp-≈ ¬Pv [] ()
  ∉-filter {P} P-resp-≈ ¬Pv (x ∷ xs) v∈fₚx∷xs with P x | inspect P x
  ... | false | _ = ∉-filter P-resp-≈ ¬Pv xs v∈fₚx∷xs 
  ... | true  | [ Px ] with v∈fₚx∷xs
  ...   | here v≈x = contradiction (≡-trans (≡-trans (≡-sym Px) (P-resp-≈ (sym v≈x))) ¬Pv) λ()
  ...   | there v∈fₚxs = ∉-filter P-resp-≈ ¬Pv xs v∈fₚxs

  gfilter-⊆ : ∀ {P Q} (xs : List A) → (∀ {x a} → Eq _≈_ (P x) (just a) → Eq _≈_ (P x) (Q x)) → gfilter P xs ⊆ gfilter Q xs
  gfilter-⊆ [] _ ()
  gfilter-⊆ {P} {Q} (x ∷ xs) P⇨Q v∈gfₚx∷xs with P x | Q x | inspect P x | inspect Q x
  ... | nothing | nothing | _ | _ = gfilter-⊆ xs P⇨Q v∈gfₚx∷xs
  ... | nothing | just b  | _ | _ = there (gfilter-⊆ xs P⇨Q v∈gfₚx∷xs)
  ... | just a  | nothing | [ Px≡justa ] | [ Qx≡nothing ] = contradiction (subst₂ (Eq _≈_) Px≡justa Qx≡nothing (P⇨Q (eq-reflexive ≈-refl Px≡justa))) λ()
  ... | just a  | just b  | [ Px≡justa ] | [ Qx≡justb ] with v∈gfₚx∷xs
  ...   | here x≈a = here (trans x≈a (drop-just (subst₂ (Eq _≈_) Px≡justa Qx≡justb (P⇨Q (eq-reflexive ≈-refl Px≡justa)))))
  ...   | there v∈gfₚxs = there (gfilter-⊆ xs P⇨Q v∈gfₚxs)

  filter-⊆ : ∀ {P Q} → (xs : List A) → (∀ {x} → P x ≡ true → Q x ≡ true) → filter P xs ⊆ filter Q xs
  filter-⊆ {P} {Q} xs P⇨Q = gfilter-⊆ xs P⇨Q'

    where 

    P⇨Q' : ∀ {x a : A} → Eq _≈_ (if P x then just x else nothing) (just a) → Eq _≈_ (if P x then just x else nothing) (if Q x then just x else nothing)
    P⇨Q' {x} t with P x | inspect P x
    ... | false | _ = contradiction t λ()
    ... | true  | [ Px≡true ] rewrite P⇨Q Px≡true  = just ≈-refl


  ∃-foldr : (_•_ : Op₂ A) → Selective _≈_ _•_ → ∀ i xs → (foldr _•_ i xs ≈ i) ⊎ (foldr _•_ i xs ∈ xs)
  ∃-foldr _•_ sel i []       = inj₁ ≈-refl
  ∃-foldr _•_ sel i (x ∷ xs) with sel x (foldr _•_ i xs) | ∃-foldr _•_ sel i xs
  ... | inj₁ x•f≈x | _         = inj₂ (∈-resp-≈ (here ≈-refl) (sym x•f≈x))
  ... | inj₂ x•f≈f | inj₁ f≈i  = inj₁ (trans x•f≈f f≈i)
  ... | inj₂ x•f≈f | inj₂ f∈xs = inj₂ (∈-resp-≈ (there f∈xs) (sym x•f≈f))


  {-
  postulate filter-∈ : ∀ {v P xs} → v ∈ filter P xs → v ∈ xs
  

  postulate filter-reject : ∀ {v} xs P → P v ≡ false → v ∉ filter P xs

  

  gfilter-⊆ {_} {_} []       _   () 
  gfilter-⊆ {P} {Q} (x ∷ xs) P⇨Q v∈fₚx∷xs with P x | inspect P x | Q x | inspect Q x | v∈fₚx∷xs
  ... | nothing  | _            | nothing | _              | _ = (gfilter-⊆ xs P⇨Q) v∈fₚx∷xs
  ... | nothing  | _            | just b  | _              | _ = (⊆-extendᵣ b (gfilter-⊆ xs P⇨Q)) v∈fₚx∷xs
  ... | just a   | [ Px≡justa ] | nothing | [ Qx≡nothing ] | _ = contradiction (P⇨Q Px≡justa) (λ Qx≡justa → contradiction (≡-trans (≡-sym Qx≡justa) Qx≡nothing) (λ())) 
  ... | just a   | [ Px≡justa ] | just b  | [ Qx≡justb ]   | here v≈a     = here (trans v≈a (reflexive (lemma (≡-trans (≡-sym (P⇨Q Px≡justa)) Qx≡justb))))
  ... | just a   | _            | just b  | _              | there v∈fₚxs = there ((gfilter-⊆ xs P⇨Q) v∈fₚxs)

  
  --filter-implication xs P⇨Q = gfilter-implication xs (λ Px≡true → {!!})

-}

